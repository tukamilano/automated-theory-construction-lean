from __future__ import annotations

import re
from pathlib import Path
from typing import Any

from materials_pipeline import default_materials_cache_dir
from materials_pipeline import enrich_source_link_entries_with_cache
from materials_pipeline import load_cached_paper_records
from materials_pipeline import parse_source_link_entries


DEFAULT_MATERIALS_DIR = Path("materials")
TEXT_EXTENSIONS = {".md", ".markdown", ".txt", ".json", ".jsonl", ".yaml", ".yml"}
MAX_DOCUMENT_EXCERPT_CHARS = 400
MAX_LIST_ITEMS_PER_SECTION = 12
MAX_SOURCE_LINKS = 20
KIND_SECTION_TARGETS = {
    "section_map": (
        ("problem generation", "problem_generation"),
        ("problem evaluation", "problem_evaluation"),
    ),
    "source_links": (("source links", "source_links"),),
}


def empty_materials() -> dict[str, Any]:
    return {}


def _classify_material_kind(path: Path) -> str:
    stem = path.stem.lower()
    name = path.name.lower()
    if path.suffix.lower() == ".pdf":
        return "pdf"
    if stem in {"00_index", "index"}:
        return "index"
    if "section_map" in stem:
        return "section_map"
    if "source_links" in stem or "sources" in stem:
        return "source_links"
    if "research" in stem or "report" in stem or "survey" in stem:
        return "report"
    if name.endswith(".md"):
        return "markdown"
    if path.suffix.lower() in TEXT_EXTENSIONS:
        return "text"
    return "binary"


def _read_text_excerpt(path: Path) -> tuple[str, bool]:
    text = path.read_text(encoding="utf-8")
    compact = " ".join(text.split())
    if not compact:
        return "", False
    if len(compact) <= MAX_DOCUMENT_EXCERPT_CHARS:
        return compact, False
    return compact[: MAX_DOCUMENT_EXCERPT_CHARS - 3].rstrip() + "...", True


def _extract_title(path: Path, text: str) -> str:
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("#"):
            return stripped.lstrip("#").strip()
    return path.stem.replace("_", " ").strip()


def _strip_list_marker(line: str) -> str:
    cleaned = re.sub(r"^\s*(?:[-*+]|\d+\.)\s*", "", line).strip()
    cleaned = re.sub(r"^\*\*(.+?)\*\*$", r"\1", cleaned)
    return cleaned


def _parse_markdown_sections(text: str) -> dict[str, list[str]]:
    sections: dict[str, list[str]] = {}
    current_section = ""

    def current_limit() -> int:
        if current_section == "source links":
            return MAX_SOURCE_LINKS
        return MAX_LIST_ITEMS_PER_SECTION

    for raw_line in text.splitlines():
        line = raw_line.rstrip()
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("#"):
            heading = stripped.lstrip("#").strip()
            current_section = heading.lower()
            sections.setdefault(current_section, [])
            continue
        if re.match(r"^\s*(?:[-*+]|\d+\.)\s+", line):
            item = _strip_list_marker(line)
            if not item or not current_section:
                continue
            items = sections.setdefault(current_section, [])
            if item not in items and len(items) < current_limit():
                items.append(item)
            continue
        if current_section and sections.get(current_section) and re.match(r"^\s{2,}\S", line):
            items = sections[current_section]
            items[-1] = items[-1].rstrip(":") + " " + stripped
    return sections


def _append_unique(target: list[str], values: list[str], *, max_items: int) -> None:
    for value in values:
        cleaned = str(value).strip()
        if not cleaned or cleaned in target:
            continue
        target.append(cleaned)
        if len(target) >= max_items:
            return


def _strip_usage_prefix(item: str) -> str:
    return re.sub(
        r"^(problem generation|problem evaluation):?\s*",
        "",
        item,
        flags=re.IGNORECASE,
    ).strip()


def _document_confidence(*, kind: str, truncated: bool) -> str:
    if kind == "report" or truncated:
        return "medium"
    return "high"


def _append_usage_item(
    item: str,
    *,
    problem_generation: list[str],
    problem_evaluation: list[str],
) -> None:
    lowered = item.lower()
    stripped_item = _strip_usage_prefix(item)
    if lowered.startswith("problem generation"):
        _append_unique(problem_generation, [stripped_item], max_items=MAX_LIST_ITEMS_PER_SECTION)
    elif lowered.startswith("problem evaluation"):
        _append_unique(problem_evaluation, [stripped_item], max_items=MAX_LIST_ITEMS_PER_SECTION)


def _merge_kind_sections(
    *,
    kind: str,
    sections: dict[str, list[str]],
    problem_generation: list[str],
    problem_evaluation: list[str],
    source_links: list[str],
) -> None:
    if kind == "index":
        for item in sections.get("usage", []):
            _append_usage_item(
                item,
                problem_generation=problem_generation,
                problem_evaluation=problem_evaluation,
            )
        return

    target_lists = {
        "problem_generation": problem_generation,
        "problem_evaluation": problem_evaluation,
        "source_links": source_links,
    }
    for section_name, target_name in KIND_SECTION_TARGETS.get(kind, ()):
        _append_unique(
            target_lists[target_name],
            sections.get(section_name, []),
            max_items=MAX_SOURCE_LINKS if target_name == "source_links" else MAX_LIST_ITEMS_PER_SECTION,
        )


def _append_prompt_line(blocks: list[str], payload: dict[str, Any], field: str, prefix: str, *, limit: int) -> None:
    values = payload.get(field)
    if not isinstance(values, list):
        return
    rendered = [str(item).strip() for item in values if str(item).strip()]
    if not rendered:
        return
    blocks.append(prefix + "; ".join(rendered[:limit]) + "\n")


def load_materials(materials_dir: Path) -> dict[str, Any]:
    root = Path(materials_dir)
    if not root.exists() or not root.is_dir():
        return empty_materials()

    documents: list[dict[str, Any]] = []
    problem_generation: list[str] = []
    problem_evaluation: list[str] = []
    source_links: list[str] = []

    for path in sorted(item for item in root.rglob("*") if item.is_file() and not item.name.startswith(".")):
        kind = _classify_material_kind(path)
        rel_path = str(path.relative_to(root))
        document: dict[str, Any] = {
            "path": rel_path,
            "kind": kind,
            "title": path.stem.replace("_", " "),
            "confidence": "low",
            "content_available": False,
        }

        if kind in {"pdf", "binary"}:
            documents.append(document)
            continue

        try:
            text = path.read_text(encoding="utf-8")
        except Exception:
            documents.append(document)
            continue

        title = _extract_title(path, text)
        excerpt, truncated = _read_text_excerpt(path)
        document.update(
            {
                "title": title,
                "confidence": _document_confidence(kind=kind, truncated=truncated),
                "content_available": True,
                "excerpt": excerpt,
            }
        )
        documents.append(document)

        sections = _parse_markdown_sections(text)
        _merge_kind_sections(
            kind=kind,
            sections=sections,
            problem_generation=problem_generation,
            problem_evaluation=problem_evaluation,
            source_links=source_links,
        )

    if not documents:
        return empty_materials()

    cache_dir = default_materials_cache_dir(root)
    source_link_entries = enrich_source_link_entries_with_cache(parse_source_link_entries(source_links), cache_dir)
    paper_cache = load_cached_paper_records(cache_dir)

    return {
        "materials_dir": str(root.resolve()),
        "materials_cache_dir": str(cache_dir.resolve()),
        "documents": documents,
        "problem_generation": problem_generation,
        "problem_evaluation": problem_evaluation,
        "source_links": source_links,
        "source_link_entries": source_link_entries,
        "paper_cache": paper_cache,
        "notes": [
            "Treat materials as optional external context rather than internal state.",
            "If some documents are unreadable or low-confidence, degrade reliance instead of discarding all materials.",
            "Treat secondary research reports or surveys as potentially stale summaries; use source links or primary papers for novelty-sensitive judgments.",
            "If `paper_cache` is available, prefer cached paper chunks over only title-level source-link guesses.",
        ],
    }


def format_materials_prompt_block(materials: dict[str, Any] | None) -> str:
    payload = dict(materials or {})
    documents = payload.get("documents")
    if not isinstance(documents, list) or not documents:
        return ""

    blocks: list[str] = [
        "- External literature materials are available as optional context. Treat them as external anchors, not as internal state.\n",
        "- Prefer higher-confidence readable materials first. If some documents are unreadable or low-confidence, lower reliance rather than ignoring all materials.\n",
        "- Treat summary reports or surveys as possibly out of date. For novelty-sensitive or closest-known-result judgments, prefer `source_links` or primary papers when available.\n",
    ]
    _append_prompt_line(
        blocks,
        payload,
        "problem_generation",
        "- Outward-looking problem-generation anchors from materials: ",
        limit=6,
    )
    _append_prompt_line(
        blocks,
        payload,
        "problem_evaluation",
        "- Materials-based evaluation checks: ",
        limit=5,
    )
    _append_prompt_line(
        blocks,
        payload,
        "source_links",
        "- Source links are available for deeper follow-up if a candidate needs literature positioning: ",
        limit=3,
    )
    paper_cache = payload.get("paper_cache")
    if isinstance(paper_cache, list) and paper_cache:
        rendered_titles = []
        for item in paper_cache[:3]:
            if not isinstance(item, dict):
                continue
            title = str(item.get("title", "")).strip() or str(item.get("source_id", "")).strip()
            if title:
                rendered_titles.append(title)
        if rendered_titles:
            blocks.append(
                "- Cached paper extracts are available for direct reading: "
                + "; ".join(rendered_titles)
                + "\n"
            )

    return "".join(blocks)
