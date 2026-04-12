from __future__ import annotations

import hashlib
import importlib
import json
import mimetypes
import os
import re
import sys
import subprocess
from html import unescape
from html.parser import HTMLParser
from pathlib import Path
from typing import Any
from urllib.parse import urlparse


DEFAULT_MATERIALS_CACHE_DIR = Path("data/materials_cache")
DOWNLOADS_DIRNAME = "downloads"
PAPERS_DIRNAME = "papers"
DOWNLOAD_INDEX_FILENAME = "download_index.json"
MAX_PAPER_CACHE_ENTRIES = 12
MAX_PAPER_CACHE_CHUNKS = 8
MAX_PAPER_CHUNK_CHARS = 900
URL_RE = re.compile(r"https?://[^\s)>\]]+")
MARKDOWN_LINK_RE = re.compile(r"\[([^\]]+)\]\((https?://[^)]+)\)")
WHITESPACE_RE = re.compile(r"\s+")
SECTION_HEADING_RE = re.compile(r"^\s*(abstract|introduction|related work|preliminaries|conclusion|references)\s*$", re.IGNORECASE)
JSONISH_RE = re.compile(r'^\s*[\[{].*[\]}]\s*$', re.DOTALL)
NOISY_TEXT_RE = re.compile(
    r"(cookie|javascript|function\s*\(|gtag\(|datalayer|optanon|sign up|log in|skip to main|stack exchange network|@context|containerelementid|returnurl|googleclientid)",
    re.IGNORECASE,
)
BLOCKED_TAGS = {"script", "style", "noscript", "svg", "canvas", "iframe", "footer", "nav", "aside", "form"}
CONTENT_TAGS = {"article", "main", "section", "div", "p", "li", "blockquote"}
HEADING_TAGS = {"h1", "h2", "h3"}
PREFERRED_SECTIONS = ("abstract", "introduction", "overview", "summary", "main results", "results", "conclusion")
DEFAULT_EXTRA_PDF_SITE_DIRS = ("/tmp/atc_pdfdeps",)
PORTAL_REDIRECT_RE = re.compile(
    r"(redirecting to sso login|dspace software copyright|privacy policy|end user agreement|send feedback)",
    re.IGNORECASE,
)
QNA_TEXT_RE = re.compile(
    r"(ask question asked|modified \d+ years|\$\\begingroup\$|you must to answer this question)",
    re.IGNORECASE,
)


def default_materials_cache_dir(materials_dir: Path) -> Path:
    env_override = os.getenv("ATC_MATERIALS_CACHE_DIR", "").strip()
    if env_override:
        return Path(env_override)
    return materials_dir.parent / DEFAULT_MATERIALS_CACHE_DIR


def _load_pdf_reader_class() -> tuple[type[Any] | None, str]:
    candidate_site_dirs: list[str] = []
    env_text = os.getenv("ATC_MATERIALS_EXTRA_SITE_DIRS", "").strip()
    if env_text:
        candidate_site_dirs.extend(item.strip() for item in env_text.split(os.pathsep) if item.strip())
    candidate_site_dirs.extend(DEFAULT_EXTRA_PDF_SITE_DIRS)

    for module_name in ("pypdf", "PyPDF2"):
        try:
            module = importlib.import_module(module_name)
            reader_class = getattr(module, "PdfReader", None)
            if reader_class is not None:
                return reader_class, module_name
        except Exception:
            pass

    for site_dir in candidate_site_dirs:
        if not site_dir or not Path(site_dir).exists() or site_dir in sys.path:
            continue
        sys.path.insert(0, site_dir)
        for module_name in ("pypdf", "PyPDF2"):
            try:
                module = importlib.import_module(module_name)
                reader_class = getattr(module, "PdfReader", None)
                if reader_class is not None:
                    return reader_class, module_name
            except Exception:
                continue

    return None, ""


def parse_source_link_entry(raw: str) -> dict[str, str] | None:
    text = str(raw).strip()
    if not text:
        return None

    markdown_match = MARKDOWN_LINK_RE.search(text)
    if markdown_match:
        link_text = markdown_match.group(1).strip()
        url = markdown_match.group(2).strip()
    else:
        url_match = URL_RE.search(text)
        if url_match is None:
            return None
        link_text = ""
        url = url_match.group(0).strip().rstrip(".,;")

    label = text
    label = MARKDOWN_LINK_RE.sub(lambda match: match.group(1).strip(), label)
    label = URL_RE.sub("", label)
    label = re.sub(r"^\s*(?:[-*+]|\d+\.)\s*", "", label).strip()
    label = re.sub(r"\s*,?\s*accessed on [A-Za-z]+ \d{1,2}, \d{4}\s*", " ", label, flags=re.IGNORECASE)
    label = label.strip(" ,;-")
    if not label:
        label = link_text or url

    note = ""
    if link_text and link_text != label:
        note = link_text

    source_metadata = classify_source_reference(label=label, url=url)
    return {
        "label": WHITESPACE_RE.sub(" ", label).strip(),
        "url": url,
        "note": WHITESPACE_RE.sub(" ", note).strip(),
        "source_kind": str(source_metadata.get("source_kind", "")).strip(),
        "retrieval_priority": str(source_metadata.get("retrieval_priority", "")).strip(),
        "direct_reading_access": str(source_metadata.get("direct_reading_access", "")).strip(),
    }


def parse_source_link_entries(raw_items: list[str]) -> list[dict[str, str]]:
    entries: list[dict[str, str]] = []
    seen_urls: set[str] = set()
    for raw in raw_items:
        parsed = parse_source_link_entry(raw)
        if parsed is None:
            continue
        url = parsed["url"]
        if url in seen_urls:
            continue
        seen_urls.add(url)
        entries.append(parsed)
    return entries


def classify_source_reference(
    *,
    label: str,
    url: str,
    content_type: str = "",
    title: str = "",
    abstract: str = "",
) -> dict[str, str]:
    parsed = urlparse(url)
    host = parsed.netloc.lower()
    path = parsed.path.lower()
    text = " ".join(part for part in (label, title, abstract) if part).lower()
    lowered_type = content_type.lower()
    lowered_title = title.strip().lower()

    source_kind = "web_page"
    retrieval_priority = "medium"
    direct_reading_access = "unclear"

    if lowered_title in {"dspace", "redirecting to sso login"}:
        source_kind = "portal_redirect"
        retrieval_priority = "exclude"
        direct_reading_access = "blocked"
    elif any(token in host for token in ("stackexchange.com", "stackoverflow.com", "mathoverflow.net", "reddit.com")):
        source_kind = "qna"
        retrieval_priority = "exclude"
        direct_reading_access = "discussion"
    elif "plato.stanford.edu" in host:
        source_kind = "encyclopedia"
        retrieval_priority = "medium"
        direct_reading_access = "direct_fulltext"
    elif "arxiv.org" in host:
        if "/pdf/" in path or path.endswith(".pdf"):
            source_kind = "preprint_pdf"
            retrieval_priority = "high"
            direct_reading_access = "direct_fulltext"
        else:
            source_kind = "preprint_abstract"
            retrieval_priority = "medium"
            direct_reading_access = "abstract_page"
    elif "drops.dagstuhl.de" in host:
        source_kind = "proceedings_pdf" if path.endswith(".pdf") else "proceedings_page"
        retrieval_priority = "high" if path.endswith(".pdf") else "medium"
        direct_reading_access = "direct_fulltext" if path.endswith(".pdf") else "landing_page"
    elif any(token in host for token in ("researchgate.net", "semanticscholar.org", "scispace.com", "research-portal.")):
        source_kind = "metadata_portal"
        retrieval_priority = "low"
        direct_reading_access = "metadata_only"
    elif path.endswith(".pdf") or "/download" in path or "/bitstream" in path:
        if any(token in host for token in ("cambridge.org", "springer.com", "acm.org", "ieee.org", "doi.org")):
            source_kind = "publisher_pdf"
        elif any(token in host for token in ("repository.", "eprints.", "archive.", "dspace.", ".edu", ".ac.uk", ".nl", ".ru")):
            source_kind = "repository_pdf"
        else:
            source_kind = "direct_pdf"
        retrieval_priority = "high"
        direct_reading_access = "direct_fulltext"
    elif "research portal" in text or "request pdf" in text:
        source_kind = "metadata_portal"
        retrieval_priority = "low"
        direct_reading_access = "metadata_only"

    if PORTAL_REDIRECT_RE.search(text):
        source_kind = "portal_redirect"
        retrieval_priority = "exclude"
        direct_reading_access = "blocked"
    elif QNA_TEXT_RE.search(text):
        source_kind = "qna"
        retrieval_priority = "exclude"
        direct_reading_access = "discussion"
    elif "html" in lowered_type and source_kind in {"repository_pdf", "direct_pdf"} and "redirect" in text:
        source_kind = "portal_redirect"
        retrieval_priority = "exclude"
        direct_reading_access = "blocked"

    return {
        "source_kind": source_kind,
        "retrieval_priority": retrieval_priority,
        "direct_reading_access": direct_reading_access,
    }


def build_source_id(*, label: str, url: str) -> str:
    parsed = urlparse(url)
    stem_parts = [part for part in re.split(r"[^A-Za-z0-9]+", f"{parsed.netloc}_{Path(parsed.path).stem}_{label}") if part]
    stem = "_".join(stem_parts[:8]).lower() or "source"
    digest = hashlib.sha256(url.encode("utf-8")).hexdigest()[:12]
    return f"{stem}_{digest}"


def _guess_extension(url: str, content_type: str) -> str:
    parsed = urlparse(url)
    suffix = Path(parsed.path).suffix.lower()
    if suffix in {".pdf", ".html", ".htm", ".txt", ".xml"}:
        return suffix
    if content_type:
        guessed = mimetypes.guess_extension(content_type.split(";")[0].strip()) or ""
        if guessed:
            return guessed
    return ".bin"


def load_download_index(cache_dir: Path) -> list[dict[str, Any]]:
    index_path = cache_dir / DOWNLOAD_INDEX_FILENAME
    if not index_path.exists():
        return []
    try:
        payload = json.loads(index_path.read_text(encoding="utf-8"))
    except Exception:
        return []
    if not isinstance(payload, dict):
        return []
    rows = payload.get("entries", [])
    if not isinstance(rows, list):
        return []
    safe_rows: list[dict[str, Any]] = []
    for item in rows:
        if not isinstance(item, dict):
            continue
        source_id = str(item.get("source_id", "")).strip()
        url = str(item.get("url", "")).strip()
        local_relpath = str(item.get("local_relpath", "")).strip()
        if not source_id or not url or not local_relpath:
            continue
        safe_rows.append(
            {
                "source_id": source_id,
                "label": str(item.get("label", "")).strip(),
                "url": url,
                "content_type": str(item.get("content_type", "")).strip(),
                "local_relpath": local_relpath,
                "fetched_at": str(item.get("fetched_at", "")).strip(),
            }
        )
    return safe_rows


def save_download_index(cache_dir: Path, entries: list[dict[str, Any]]) -> None:
    cache_dir.mkdir(parents=True, exist_ok=True)
    payload = {"entries": entries}
    (cache_dir / DOWNLOAD_INDEX_FILENAME).write_text(
        json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


def load_cached_paper_records(cache_dir: Path, *, max_entries: int = MAX_PAPER_CACHE_ENTRIES) -> list[dict[str, Any]]:
    papers_dir = cache_dir / PAPERS_DIRNAME
    if not papers_dir.exists():
        return []
    records: list[dict[str, Any]] = []
    for path in sorted(papers_dir.glob("*.json")):
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue
        if not isinstance(payload, dict):
            continue
        source_id = str(payload.get("source_id", "")).strip()
        title = str(payload.get("title", "")).strip()
        source_url = str(payload.get("source_url", "")).strip()
        if not source_id or not source_url:
            continue
        chunks_value = payload.get("chunks", [])
        chunks: list[dict[str, Any]] = []
        if isinstance(chunks_value, list):
            for item in chunks_value[:MAX_PAPER_CACHE_CHUNKS]:
                if not isinstance(item, dict):
                    continue
                text = str(item.get("text", "")).strip()
                if not text:
                    continue
                chunks.append(
                    {
                        "chunk_id": str(item.get("chunk_id", "")).strip(),
                        "section": str(item.get("section", "")).strip(),
                        "page": item.get("page"),
                        "text": text[:MAX_PAPER_CHUNK_CHARS],
                    }
                )
        abstract = str(payload.get("abstract", "")).strip()[:MAX_PAPER_CHUNK_CHARS]
        title_text = title or str(payload.get("label", "")).strip()
        source_metadata = classify_source_reference(
            label=str(payload.get("label", "")).strip() or title_text,
            url=source_url,
            content_type=str(payload.get("content_type", "")).strip(),
            title=title_text,
            abstract=abstract,
        )
        if source_metadata["source_kind"] == "portal_redirect":
            chunks = []
            abstract = ""
        records.append(
            {
                "source_id": source_id,
                "title": title,
                "source_url": source_url,
                "content_type": str(payload.get("content_type", "")).strip(),
                "extract_confidence": str(payload.get("extract_confidence", "")).strip(),
                "abstract": abstract,
                "chunks": chunks,
                "paper_relpath": str(path.relative_to(cache_dir)),
                "source_kind": source_metadata["source_kind"],
                "retrieval_priority": source_metadata["retrieval_priority"],
                "direct_reading_access": source_metadata["direct_reading_access"],
            }
        )
    return records[:max_entries]


def _compact_text(text: str) -> str:
    return WHITESPACE_RE.sub(" ", text).strip()


class _SimpleHTMLTextExtractor(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.title = ""
        self._in_title = False
        self._blocked_depth = 0
        self._current_heading = ""
        self._chunks: list[tuple[str, str]] = []
        self._text_parts: list[str] = []
        self._current_tag = ""

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag in BLOCKED_TAGS:
            self._blocked_depth += 1
            return
        if self._blocked_depth > 0:
            return
        if tag == "title":
            self._in_title = True
            return
        self._current_tag = tag
        if tag in HEADING_TAGS:
            self._flush_text()
            self._current_heading = ""
        elif tag in CONTENT_TAGS or tag == "br":
            self._text_parts.append("\n")

    def handle_endtag(self, tag: str) -> None:
        if tag in BLOCKED_TAGS:
            if self._blocked_depth > 0:
                self._blocked_depth -= 1
            return
        if self._blocked_depth > 0:
            return
        if tag == "title":
            self._in_title = False
            return
        if tag in HEADING_TAGS:
            heading = _compact_text("".join(self._text_parts))
            self._text_parts = []
            if heading:
                self._current_heading = heading
        elif tag in CONTENT_TAGS:
            self._flush_text()

    def handle_data(self, data: str) -> None:
        if self._blocked_depth > 0:
            return
        if self._in_title:
            self.title += data
            return
        stripped = data.strip()
        if not stripped:
            self._text_parts.append(data)
            return
        if JSONISH_RE.match(stripped):
            return
        if NOISY_TEXT_RE.search(stripped):
            return
        self._text_parts.append(data)

    def _flush_text(self) -> None:
        text = _compact_text(unescape(" ".join(self._text_parts)))
        self._text_parts = []
        if text:
            lowered = text.lower()
            if len(text) < 20 and not self._current_heading:
                return
            if JSONISH_RE.match(text):
                return
            if NOISY_TEXT_RE.search(text):
                return
            if lowered.startswith("skip to main") or lowered.startswith("sign up or log in"):
                return
            self._chunks.append((self._current_heading, text))

    def result(self) -> tuple[str, list[tuple[str, str]]]:
        self._flush_text()
        return _compact_text(self.title), self._chunks


def _chunk_paragraphs(paragraphs: list[tuple[str, str]]) -> list[dict[str, Any]]:
    chunks: list[dict[str, Any]] = []
    chunk_index = 1
    current_section = ""
    buffer = ""

    def flush() -> None:
        nonlocal chunk_index, buffer
        text = _compact_text(buffer)
        if not text:
            buffer = ""
            return
        chunks.append(
            {
                "chunk_id": f"chunk_{chunk_index:03d}",
                "section": current_section,
                "page": None,
                "text": text,
            }
        )
        chunk_index += 1
        buffer = ""

    for section, text in paragraphs:
        if section and section != current_section:
            flush()
            current_section = section
        candidate = (buffer + "\n\n" + text).strip() if buffer else text
        if len(candidate) > MAX_PAPER_CHUNK_CHARS and buffer:
            flush()
            buffer = text
        else:
            buffer = candidate
    flush()
    return chunks


def _score_chunk(chunk: dict[str, Any]) -> tuple[int, int]:
    section = str(chunk.get("section", "")).strip().lower()
    text = str(chunk.get("text", "")).strip()
    lowered = text.lower()
    score = 0
    for index, preferred in enumerate(PREFERRED_SECTIONS):
        if preferred in section:
            score += 100 - index
    if "lambek" in lowered:
        score += 20
    if "substructural" in lowered:
        score += 15
    if "abstract" in section:
        score += 20
    if len(text) >= 120:
        score += 5
    if NOISY_TEXT_RE.search(text):
        score -= 100
    if JSONISH_RE.match(text):
        score -= 100
    return score, len(text)


def _filter_chunks(chunks: list[dict[str, Any]]) -> list[dict[str, Any]]:
    scored = []
    for chunk in chunks:
        text = str(chunk.get("text", "")).strip()
        if not text:
            continue
        if NOISY_TEXT_RE.search(text) or JSONISH_RE.match(text):
            continue
        scored.append(( _score_chunk(chunk), chunk))
    scored.sort(key=lambda item: (item[0][0], item[0][1]), reverse=True)
    return [chunk for _, chunk in scored[:40]]


def _extract_html_record(download_path: Path, *, source_id: str, source_url: str, label: str, content_type: str) -> dict[str, Any]:
    text = download_path.read_text(encoding="utf-8", errors="ignore")
    parser = _SimpleHTMLTextExtractor()
    parser.feed(text)
    title, paragraphs = parser.result()
    chunks = _filter_chunks(_chunk_paragraphs(paragraphs))
    abstract = ""
    for section, paragraph in paragraphs:
        if section and SECTION_HEADING_RE.match(section) and section.lower() == "abstract":
            abstract = paragraph
            break
    if not abstract and chunks:
        abstract = chunks[0]["text"]
    source_metadata = classify_source_reference(
        label=label,
        url=source_url,
        content_type=content_type or "text/html",
        title=title or label,
        abstract=abstract,
    )
    if source_metadata["source_kind"] == "portal_redirect":
        chunks = []
        abstract = ""
    return {
        "source_id": source_id,
        "source_url": source_url,
        "label": label,
        "title": title or label,
        "content_type": content_type or "text/html",
        "extract_confidence": "high" if chunks else "low",
        "abstract": abstract[:MAX_PAPER_CHUNK_CHARS],
        "chunks": chunks[:40],
        "source_kind": source_metadata["source_kind"],
        "retrieval_priority": source_metadata["retrieval_priority"],
        "direct_reading_access": source_metadata["direct_reading_access"],
    }


def _extract_pdf_text(download_path: Path) -> tuple[str, str]:
    pdf_reader_class, module_name = _load_pdf_reader_class()
    if pdf_reader_class is not None:
        try:
            reader = pdf_reader_class(str(download_path))
            pages = [(page.extract_text() or "").strip() for page in reader.pages]
            text = "\n\n".join(page for page in pages if page)
            if text.strip():
                confidence = "high" if module_name == "pypdf" else "medium"
                return text, confidence
        except Exception:
            pass

    pdftotext = shutil_which("pdftotext")
    if pdftotext:
        completed = subprocess.run(
            [pdftotext, "-layout", str(download_path), "-"],
            capture_output=True,
            text=True,
            check=False,
        )
        if completed.returncode == 0 and completed.stdout.strip():
            return completed.stdout, "medium"
    return "", "low"


def shutil_which(command: str) -> str | None:
    for directory in os.getenv("PATH", "").split(os.pathsep):
        if not directory:
            continue
        candidate = Path(directory) / command
        if candidate.exists() and os.access(candidate, os.X_OK):
            return str(candidate)
    return None


def _extract_pdf_record(download_path: Path, *, source_id: str, source_url: str, label: str, content_type: str) -> dict[str, Any]:
    text, confidence = _extract_pdf_text(download_path)
    paragraphs = [( "", paragraph.strip()) for paragraph in re.split(r"\n\s*\n+", text) if paragraph.strip()]
    chunks = _filter_chunks(_chunk_paragraphs(paragraphs))
    abstract = chunks[0]["text"][:MAX_PAPER_CHUNK_CHARS] if chunks else ""
    source_metadata = classify_source_reference(
        label=label,
        url=source_url,
        content_type=content_type or "application/pdf",
        title=label,
        abstract=abstract,
    )
    return {
        "source_id": source_id,
        "source_url": source_url,
        "label": label,
        "title": label,
        "content_type": content_type or "application/pdf",
        "extract_confidence": confidence,
        "abstract": abstract,
        "chunks": chunks[:40],
        "source_kind": source_metadata["source_kind"],
        "retrieval_priority": source_metadata["retrieval_priority"],
        "direct_reading_access": source_metadata["direct_reading_access"],
    }


def extract_paper_record(download_path: Path, *, source_id: str, source_url: str, label: str, content_type: str) -> dict[str, Any]:
    lowered_type = content_type.lower()
    suffix = download_path.suffix.lower()
    if "html" in lowered_type or suffix in {".html", ".htm"}:
        return _extract_html_record(
            download_path,
            source_id=source_id,
            source_url=source_url,
            label=label,
            content_type=content_type,
        )
    if "pdf" in lowered_type or suffix == ".pdf":
        return _extract_pdf_record(
            download_path,
            source_id=source_id,
            source_url=source_url,
            label=label,
            content_type=content_type,
        )
    text = download_path.read_text(encoding="utf-8", errors="ignore")
    paragraphs = [("", paragraph.strip()) for paragraph in re.split(r"\n\s*\n+", text) if paragraph.strip()]
    chunks = _filter_chunks(_chunk_paragraphs(paragraphs))
    abstract = chunks[0]["text"][:MAX_PAPER_CHUNK_CHARS] if chunks else ""
    source_metadata = classify_source_reference(
        label=label,
        url=source_url,
        content_type=content_type or "text/plain",
        title=label,
        abstract=abstract,
    )
    return {
        "source_id": source_id,
        "source_url": source_url,
        "label": label,
        "title": label,
        "content_type": content_type or "text/plain",
        "extract_confidence": "medium" if chunks else "low",
        "abstract": abstract,
        "chunks": chunks[:40],
        "source_kind": source_metadata["source_kind"],
        "retrieval_priority": source_metadata["retrieval_priority"],
        "direct_reading_access": source_metadata["direct_reading_access"],
    }


def save_paper_record(cache_dir: Path, record: dict[str, Any]) -> Path:
    papers_dir = cache_dir / PAPERS_DIRNAME
    papers_dir.mkdir(parents=True, exist_ok=True)
    source_id = str(record.get("source_id", "")).strip()
    if not source_id:
        raise ValueError("paper record missing source_id")
    output_path = papers_dir / f"{source_id}.json"
    output_path.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return output_path


def build_download_metadata(*, label: str, url: str, content_type: str, local_relpath: str) -> dict[str, Any]:
    return {
        "source_id": build_source_id(label=label, url=url),
        "label": label,
        "url": url,
        "content_type": content_type,
        "local_relpath": local_relpath,
    }


def choose_download_filename(*, label: str, url: str, content_type: str) -> str:
    source_id = build_source_id(label=label, url=url)
    return source_id + _guess_extension(url, content_type)
