from __future__ import annotations

import re
import sys
import threading
import time
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
SCRIPTS_ROOT = SCRIPT_DIR.parent
LOOP_ROOT = SCRIPTS_ROOT / "loop"
for search_path in (SCRIPTS_ROOT, LOOP_ROOT):
    search_path_str = str(search_path)
    if search_path_str not in sys.path:
        sys.path.insert(0, search_path_str)

from common import append_jsonl
from common import normalize_open_problem_row
from common import read_archived_problem_rows
from common import read_jsonl
from formalization_runtime import attempt_formalization_until_timeout
from generated_library import render_scratch_template
from guidance import unpack_guidance_context
from loop_common import iso_timestamp_now
from loop_common import monotonic_duration_ms
from loop_helpers import append_derived_entry_cache
from loop_helpers import append_phase_attempt_record
from loop_helpers import build_problem_theory_context
from loop_helpers import emit_phase_log
from loop_helpers import extract_theorem_code_from_scratch
from loop_helpers import is_verified_resolution
from loop_helpers import load_current_guidance
from loop_helpers import load_formalization_memory
from loop_helpers import load_theory_state
from loop_helpers import open_problem_priority_label
from loop_helpers import shortlist_relevant_derived_entries
from loop_helpers import validate_theorem_name_stem
from problem_expansion import request_expand_candidates
from problem_expansion import store_expand_candidates_and_refresh
from prompt_loader import load_prompt_file
from main_theorem_rejection_memory import append_main_theorem_rejection_entry
from main_theorem_rejection_memory import load_main_theorem_rejection_memory
from materials_sync import ensure_materials_cache_current
from theorem_commit import commit_verified_theorem_and_generation
from theorem_reuse_memory import append_theorem_reuse_memory_entry
from worker_client import invoke_worker_json


SCRATCH_TEMPLATE = render_scratch_template()
MAX_EXPAND_CANDIDATES_PER_MAIN_THEOREM = 5
MAIN_THEOREM_CANDIDATE_COUNT = 3
MAIN_THEOREM_PATTERNS = {"new_theorem", "structure_discovery", "framework_introduction"}
MAIN_THEOREM_REJECTION_MEMORY_FILENAME = "main_theorem_rejection_memory.json"
MAX_MAIN_THEOREM_REJECTION_ATTEMPTS = 20
MAX_VISIBLE_REJECTED_CANDIDATES = 12
MAX_RETRIEVAL_QUERY_TERMS = 32
MAX_RETRIEVAL_SOURCE_LINKS = 8
MAX_RETRIEVAL_DOCUMENTS = 8
MAX_RETRIEVAL_MAIN_THEOREM_NOTES = 6
MAX_RETRIEVAL_PAPERS = 4
MAX_RETRIEVAL_PAPER_CHUNKS = 3
MAX_RETRIEVAL_CHUNK_CHARS = 500
RETRIEVAL_TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9_+-]{2,}")
RETRIEVAL_STOPWORDS = {
    "about",
    "against",
    "among",
    "and",
    "candidate",
    "condition",
    "context",
    "does",
    "from",
    "have",
    "into",
    "lemma",
    "logic",
    "main",
    "mapping",
    "more",
    "note",
    "paper",
    "problem",
    "proof",
    "result",
    "show",
    "some",
    "statement",
    "such",
    "than",
    "that",
    "theorem",
    "their",
    "there",
    "these",
    "this",
    "those",
    "through",
    "under",
    "using",
    "with",
}
RETRIEVAL_SOURCE_KIND_BONUS = {
    "preprint_pdf": 10,
    "proceedings_pdf": 10,
    "publisher_pdf": 10,
    "repository_pdf": 8,
    "direct_pdf": 8,
    "scanned_pdf_ocr": 4,
    "scanned_pdf": -6,
    "encyclopedia": 5,
    "preprint_abstract": 3,
    "proceedings_page": 2,
    "web_page": 0,
    "metadata_portal": -8,
    "portal_redirect": -24,
    "qna": -24,
}
RETRIEVAL_PRIORITY_BONUS = {
    "high": 6,
    "medium": 2,
    "low": -4,
    "exclude": -20,
}


def load_prompt_text(prompt_file: str) -> str:
    return load_prompt_file(Path(prompt_file))


def _build_main_theorem_followup_candidates(
    *,
    theorem_name: str,
    statement: str,
    rationale: str,
    verify_error_excerpt: str,
    missing_lemmas: list[str],
    intermediate_lemmas: list[str],
) -> list[dict[str, str]]:
    candidates: list[dict[str, str]] = []
    seen_stmt_norms: set[str] = set()

    def add_candidate(raw_statement: str, raw_rationale: str) -> None:
        stmt = str(raw_statement).strip()
        if not stmt:
            return
        norm = " ".join(stmt.split()).lower()
        if not norm or norm in seen_stmt_norms:
            return
        seen_stmt_norms.add(norm)
        candidates.append(
            {
                "statement": stmt,
                "rationale": str(raw_rationale).strip(),
            }
        )

    if statement.strip():
        add_candidate(
            statement,
            verify_error_excerpt.strip()
            or rationale.strip()
            or f"Main theorem candidate `{theorem_name}` remained unresolved.",
        )
    for item in missing_lemmas:
        add_candidate(item, f"Missing lemma needed for `{theorem_name}`.")
    for item in intermediate_lemmas:
        add_candidate(item, f"Intermediate lemma suggested while proving `{theorem_name}`.")
    return candidates


def _summarize_main_theorem_candidates(candidates: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "candidate_rank_seed": int(candidate["candidate_rank_seed"]),
            "theorem_name_stem": str(candidate["theorem_name_stem"]),
            "statement": str(candidate["statement"]),
            "theorem_pattern": str(candidate["theorem_pattern"]),
        }
        for candidate in candidates
    ]


def _summarize_main_theorem_ranking(
    ranking: list[dict[str, Any]],
    candidate_lookup: dict[int, dict[str, Any]],
) -> list[dict[str, Any]]:
    ranking_summary: list[dict[str, Any]] = []
    for entry in ranking:
        candidate_rank_seed = int(entry["candidate_rank_seed"])
        candidate = candidate_lookup[candidate_rank_seed]
        ranking_summary.append(
            {
                "rank": int(entry["rank"]),
                "candidate_rank_seed": candidate_rank_seed,
                "decision": str(entry["decision"]),
                "theorem_name_stem": str(candidate["theorem_name_stem"]),
                "statement": str(candidate["statement"]),
                "reason": str(entry["reason"]),
            }
        )
    return ranking_summary


def _summarize_retrieval_source_access(materials: dict[str, Any]) -> dict[str, list[dict[str, str]]]:
    payload = dict(materials or {})

    paper_access: list[dict[str, str]] = []
    raw_papers = payload.get("paper_excerpt_context", [])
    if isinstance(raw_papers, list):
        for raw_item in raw_papers[:MAX_RETRIEVAL_PAPERS]:
            if not isinstance(raw_item, dict):
                continue
            download_path = str(raw_item.get("download_path", "")).strip()
            paper_record_path = str(raw_item.get("paper_record_path", "")).strip()
            if not download_path and not paper_record_path:
                continue
            paper_access.append(
                {
                    "reference": str(raw_item.get("reference", "")).strip(),
                    "source_url": str(raw_item.get("source_url", "")).strip(),
                    "direct_reading_access": str(raw_item.get("direct_reading_access", "")).strip(),
                    "extract_confidence": str(raw_item.get("extract_confidence", "")).strip(),
                    "download_path": download_path,
                    "paper_record_path": paper_record_path,
                }
            )

    source_link_access: list[dict[str, str]] = []
    raw_links = payload.get("source_link_entries", [])
    if isinstance(raw_links, list):
        for raw_item in raw_links[:MAX_RETRIEVAL_SOURCE_LINKS]:
            if not isinstance(raw_item, dict):
                continue
            download_path = str(raw_item.get("download_path", "")).strip()
            paper_record_path = str(raw_item.get("paper_record_path", "")).strip()
            if not download_path and not paper_record_path:
                continue
            source_link_access.append(
                {
                    "label": str(raw_item.get("label", "")).strip(),
                    "url": str(raw_item.get("url", "")).strip(),
                    "source_kind": str(raw_item.get("source_kind", "")).strip(),
                    "direct_reading_access": str(raw_item.get("direct_reading_access", "")).strip(),
                    "download_path": download_path,
                    "paper_record_path": paper_record_path,
                }
            )

    return {
        "paper_access": paper_access,
        "source_link_access": source_link_access,
    }


def _append_main_theorem_session_event(
    session_events_path: Path | None,
    *,
    event: str,
    run_id: str,
    iteration: int,
    candidate_set_id: str,
    payload: dict[str, Any],
) -> None:
    if session_events_path is None:
        return
    append_jsonl(
        session_events_path,
        {
            "event": event,
            "run_id": run_id,
            "iteration": iteration,
            "candidate_set_id": candidate_set_id,
            "recorded_at": iso_timestamp_now(),
            **payload,
        },
    )


def _store_main_theorem_followups(
    *,
    data_dir: Path,
    theorem_name: str,
    statement: str,
    rationale: str,
    verify_error_excerpt: str,
    missing_lemmas: list[str],
    intermediate_lemmas: list[str],
    prioritize_open_problems_worker_settings: Any,
    prioritize_open_problems_prompt_file: str,
    derived_entries: list[dict[str, str]],
    current_iteration: int,
    failure_threshold: int,
    run_id: str,
    theory_state_history_path: Path,
    theory_file: Path,
    derived_file: Path,
    repo_root: Path,
    batch_generator_seed_count: int,
    batch_generator_open_target_min: int,
) -> dict[str, Any]:
    followup_candidates = _build_main_theorem_followup_candidates(
        theorem_name=theorem_name,
        statement=statement,
        rationale=rationale,
        verify_error_excerpt=verify_error_excerpt,
        missing_lemmas=missing_lemmas,
        intermediate_lemmas=intermediate_lemmas,
    )
    if not followup_candidates:
        return {
            "followup_candidates": [],
            "stored_expand_rows": [],
            "priority_refresh_ran": False,
            "priority_refresh_error": "",
            "priority_refresh_report": {},
        }
    refresh_outcome = store_expand_candidates_and_refresh(
        data_dir=data_dir,
        statements_with_rationale=followup_candidates,
        source="main_theorem_followup",
        source_problem_id=theorem_name,
        source_kind="main_theorem",
        prioritize_worker_settings=prioritize_open_problems_worker_settings,
        prioritizer_prompt_file=prioritize_open_problems_prompt_file,
        derived_entries=derived_entries,
        current_iteration=current_iteration,
        failure_threshold=failure_threshold,
        run_id=run_id,
        theory_state_history_path=theory_state_history_path,
        theory_file=theory_file,
        derived_file=derived_file,
        repo_root=repo_root,
        batch_generator_seed_count=batch_generator_seed_count,
        batch_generator_open_target_min=batch_generator_open_target_min,
        allow_backfill=False,
    )
    refresh_outcome["followup_candidates"] = followup_candidates
    return refresh_outcome


def _build_main_theorem_tracked_problem_payload(
    tracked_rows: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], list[str]]:
    visible_tracked_rows = tracked_rows[:40]
    payload_rows = [
        {
            "problem_id": str(row.get("id", "")),
            "stmt": str(row.get("stmt", "")),
            "priority": open_problem_priority_label(row),
            "queue_status": str(row.get("queue_status", "open")),
            "source_kind": str(row.get("source_kind", row.get("queue_status", "open"))),
            "failure_count": int(row.get("failure_count", 0) or 0),
            "mode": str(row.get("mode", "")),
            "summary_delta": str(row.get("summary_delta", "")),
        }
        for row in visible_tracked_rows
    ]
    known_problem_ids = [str(row.get("problem_id", "")).strip() for row in payload_rows if str(row.get("problem_id", "")).strip()]
    return payload_rows, known_problem_ids


def _build_main_theorem_rejected_candidate_payload(entries: list[dict[str, Any]]) -> list[dict[str, Any]]:
    visible_entries = entries[-MAX_VISIBLE_REJECTED_CANDIDATES:]
    return [
        {
            "candidate_id": str(entry.get("candidate_id", "")),
            "statement": str(entry.get("statement", "")),
            "theorem_name_stem": str(entry.get("theorem_name_stem", "")),
            "rationale": str(entry.get("rationale", "")),
            "verdict": str(entry.get("verdict", "")),
            "reason": str(entry.get("reason", "")),
            "strongest_objection": str(entry.get("strongest_objection", "")),
            "salvage_plan": str(entry.get("salvage_plan", "")),
            "paper_unit_viability": str(entry.get("paper_unit_viability", "")),
            "novelty": str(entry.get("novelty", "")),
            "significance": str(entry.get("significance", "")),
            "iteration": int(entry.get("iteration", 0) or 0),
        }
        for entry in visible_entries
    ]


def _tokenize_retrieval_text(text: str) -> list[str]:
    seen: set[str] = set()
    tokens: list[str] = []
    for raw_token in RETRIEVAL_TOKEN_RE.findall(str(text or "").lower()):
        token = raw_token.strip("_+-")
        if len(token) < 3 or token in RETRIEVAL_STOPWORDS or token in seen:
            continue
        seen.add(token)
        tokens.append(token)
    return tokens


def _truncate_retrieval_text(text: str, *, limit: int = MAX_RETRIEVAL_CHUNK_CHARS) -> str:
    compact = " ".join(str(text or "").split())
    if len(compact) <= limit:
        return compact
    return compact[: limit - 3].rstrip() + "..."


def _overlap_score(query_terms: set[str], text: str) -> int:
    if not query_terms:
        return 0
    return len(query_terms.intersection(_tokenize_retrieval_text(text)))


def _build_retrieval_query_terms(candidate: dict[str, Any]) -> list[str]:
    text_fields = [
        candidate.get("statement", ""),
        candidate.get("docstring_summary", ""),
        candidate.get("rationale", ""),
        str(candidate.get("theorem_pattern", "")).replace("_", " "),
        candidate.get("context_note", ""),
        candidate.get("conceptual_depth_note", ""),
        " ".join(str(item) for item in candidate.get("supporting_theorems", [])),
        " ".join(str(item) for item in candidate.get("missing_lemmas", [])),
    ]
    seen: set[str] = set()
    query_terms: list[str] = []
    for text in text_fields:
        for token in _tokenize_retrieval_text(str(text)):
            if token in seen:
                continue
            seen.add(token)
            query_terms.append(token)
            if len(query_terms) >= MAX_RETRIEVAL_QUERY_TERMS:
                return query_terms
    return query_terms


def _score_retrieval_chunk(query_terms: set[str], chunk: dict[str, Any]) -> int:
    section = str(chunk.get("section", "")).strip()
    text = str(chunk.get("text", "")).strip()
    section_score = _overlap_score(query_terms, section)
    text_score = _overlap_score(query_terms, text)
    score = section_score * 3 + text_score * 4
    lowered_section = section.lower()
    if "abstract" in lowered_section or "introduction" in lowered_section or "main result" in lowered_section:
        score += 1
    return score


def _select_retrieval_chunks(query_terms: set[str], record: dict[str, Any]) -> list[dict[str, Any]]:
    chunks_value = record.get("chunks", [])
    if not isinstance(chunks_value, list):
        return []
    scored_chunks: list[tuple[int, dict[str, Any]]] = []
    for chunk in chunks_value:
        if not isinstance(chunk, dict):
            continue
        text = str(chunk.get("text", "")).strip()
        if not text:
            continue
        scored_chunks.append((_score_retrieval_chunk(query_terms, chunk), chunk))
    if not scored_chunks:
        return []
    scored_chunks.sort(
        key=lambda item: (
            int(item[0]),
            len(str(item[1].get("text", "")).strip()),
        ),
        reverse=True,
    )
    positive_chunks = [item for item in scored_chunks if item[0] > 0]
    selected = positive_chunks[:MAX_RETRIEVAL_PAPER_CHUNKS] or scored_chunks[:1]
    return [
        {
            "chunk_id": str(chunk.get("chunk_id", "")).strip(),
            "section": str(chunk.get("section", "")).strip(),
            "page": chunk.get("page"),
            "text": _truncate_retrieval_text(str(chunk.get("text", "")).strip()),
            "score": int(score),
        }
        for score, chunk in selected
    ]


def _score_retrieval_paper(query_terms: set[str], record: dict[str, Any]) -> int:
    title = str(record.get("title", "")).strip()
    abstract = str(record.get("abstract", "")).strip()
    title_overlap = _overlap_score(query_terms, title)
    abstract_overlap = _overlap_score(query_terms, abstract)
    score = title_overlap * 8 + abstract_overlap * 4
    selected_chunks = _select_retrieval_chunks(query_terms, record)
    score += sum(int(item.get("score", 0) or 0) for item in selected_chunks)
    extract_confidence = str(record.get("extract_confidence", "")).strip()
    source_kind = str(record.get("source_kind", "")).strip()
    retrieval_priority = str(record.get("retrieval_priority", "")).strip()
    direct_reading_access = str(record.get("direct_reading_access", "")).strip()
    score += RETRIEVAL_SOURCE_KIND_BONUS.get(source_kind, 0)
    score += RETRIEVAL_PRIORITY_BONUS.get(retrieval_priority, 0)
    if extract_confidence == "high":
        score += 3
    elif extract_confidence == "medium":
        score += 1
    if title_overlap == 0 and abstract_overlap > 0:
        score -= 12
    elif title_overlap == 0 and selected_chunks:
        score -= 8
    if selected_chunks:
        score += 2
    elif direct_reading_access not in {"direct_fulltext", "abstract_page"}:
        score -= 3
    return score


def _build_retrieval_paper_record(query_terms: set[str], record: dict[str, Any]) -> tuple[int, dict[str, Any]]:
    selected_chunks = _select_retrieval_chunks(query_terms, record)
    score = _score_retrieval_paper(query_terms, record)
    compact_record = {
        "source_id": str(record.get("source_id", "")).strip(),
        "title": str(record.get("title", "")).strip(),
        "source_url": str(record.get("source_url", "")).strip(),
        "extract_confidence": str(record.get("extract_confidence", "")).strip(),
        "source_kind": str(record.get("source_kind", "")).strip(),
        "retrieval_priority": str(record.get("retrieval_priority", "")).strip(),
        "direct_reading_access": str(record.get("direct_reading_access", "")).strip(),
        "abstract": _truncate_retrieval_text(str(record.get("abstract", "")).strip()),
        "chunks": selected_chunks,
        "paper_relpath": str(record.get("paper_relpath", "")).strip(),
        "paper_record_relpath": str(record.get("paper_record_relpath", "")).strip(),
        "paper_record_path": str(record.get("paper_record_path", "")).strip(),
        "download_relpath": str(record.get("download_relpath", "")).strip(),
        "download_path": str(record.get("download_path", "")).strip(),
        "relevance_score": score,
    }
    return score, compact_record


def _select_retrieval_source_link_entries(
    query_terms: set[str],
    entries: list[dict[str, Any]],
    selected_source_urls: set[str],
    source_metadata_by_url: dict[str, dict[str, Any]],
) -> list[dict[str, Any]]:
    scored_entries: list[tuple[int, dict[str, Any]]] = []
    for raw_entry in entries:
        if not isinstance(raw_entry, dict):
            continue
        entry_url = str(raw_entry.get("url", "")).strip()
        cached_source_metadata = source_metadata_by_url.get(entry_url, {})
        entry = {
            "label": str(raw_entry.get("label", "")).strip(),
            "url": entry_url,
            "note": str(raw_entry.get("note", "")).strip(),
            "source_kind": str(cached_source_metadata.get("source_kind", "")).strip()
            or str(raw_entry.get("source_kind", "")).strip(),
            "retrieval_priority": str(cached_source_metadata.get("retrieval_priority", "")).strip()
            or str(raw_entry.get("retrieval_priority", "")).strip(),
            "direct_reading_access": str(cached_source_metadata.get("direct_reading_access", "")).strip()
            or str(raw_entry.get("direct_reading_access", "")).strip(),
            "download_relpath": str(cached_source_metadata.get("download_relpath", "")).strip()
            or str(raw_entry.get("download_relpath", "")).strip(),
            "download_path": str(cached_source_metadata.get("download_path", "")).strip()
            or str(raw_entry.get("download_path", "")).strip(),
            "paper_record_relpath": str(cached_source_metadata.get("paper_record_relpath", "")).strip()
            or str(raw_entry.get("paper_record_relpath", "")).strip(),
            "paper_record_path": str(cached_source_metadata.get("paper_record_path", "")).strip()
            or str(raw_entry.get("paper_record_path", "")).strip(),
        }
        if not entry["url"]:
            continue
        score = 0
        if entry["url"] in selected_source_urls:
            score += 20
        score += _overlap_score(query_terms, entry["label"]) * 4
        score += _overlap_score(query_terms, entry["note"]) * 2
        score += RETRIEVAL_SOURCE_KIND_BONUS.get(entry["source_kind"], 0)
        score += RETRIEVAL_PRIORITY_BONUS.get(entry["retrieval_priority"], 0)
        scored_entries.append((score, entry))
    scored_entries.sort(key=lambda item: (int(item[0]), len(item[1]["label"])), reverse=True)
    usable_entries = [entry for score, entry in scored_entries if score > 0 and entry["retrieval_priority"] != "exclude"]
    selected_entries = usable_entries[:MAX_RETRIEVAL_SOURCE_LINKS]
    if selected_entries:
        return selected_entries
    fallback_entries = [entry for _, entry in scored_entries if entry["retrieval_priority"] != "exclude"]
    if fallback_entries:
        return fallback_entries[:MAX_RETRIEVAL_SOURCE_LINKS]
    return [entry for _, entry in scored_entries[:MAX_RETRIEVAL_SOURCE_LINKS]]


def _select_retrieval_documents(query_terms: set[str], documents: list[dict[str, Any]]) -> list[dict[str, Any]]:
    scored_documents: list[tuple[int, dict[str, Any]]] = []
    for raw_document in documents:
        if not isinstance(raw_document, dict):
            continue
        document = {
            "path": str(raw_document.get("path", "")).strip(),
            "kind": str(raw_document.get("kind", "")).strip(),
            "title": str(raw_document.get("title", "")).strip(),
            "confidence": str(raw_document.get("confidence", "")).strip(),
            "content_available": bool(raw_document.get("content_available", False)),
        }
        excerpt = str(raw_document.get("excerpt", "")).strip()
        if excerpt:
            document["excerpt"] = _truncate_retrieval_text(excerpt, limit=260)
        score = _overlap_score(query_terms, " ".join([document["title"], document["path"], excerpt]))
        if document["kind"] in {"section_map", "report", "index"}:
            score += 1
        if document["confidence"] == "high":
            score += 1
        scored_documents.append((score, document))
    scored_documents.sort(key=lambda item: (int(item[0]), len(item[1].get("title", ""))), reverse=True)
    positive_documents = [document for score, document in scored_documents if score > 0]
    selected_documents = positive_documents[:MAX_RETRIEVAL_DOCUMENTS] or [
        document for _, document in scored_documents[:MAX_RETRIEVAL_DOCUMENTS]
    ]
    return selected_documents


def _build_main_theorem_retrieval_materials(candidate: dict[str, Any], materials: dict[str, Any]) -> dict[str, Any]:
    payload = dict(materials or {})
    if not payload:
        return {}

    query_terms = _build_retrieval_query_terms(candidate)
    query_term_set = set(query_terms)

    selected_papers: list[dict[str, Any]] = []
    raw_paper_cache = payload.get("paper_cache", [])
    if isinstance(raw_paper_cache, list):
        scored_papers: list[tuple[int, dict[str, Any]]] = []
        for raw_record in raw_paper_cache:
            if not isinstance(raw_record, dict):
                continue
            score, compact_record = _build_retrieval_paper_record(query_term_set, raw_record)
            scored_papers.append((score, compact_record))
        scored_papers.sort(
            key=lambda item: (
                int(item[0]),
                1 if str(item[1].get("extract_confidence", "")).strip() == "high" else 0,
            ),
            reverse=True,
        )
        usable_papers = [record for _, record in scored_papers if str(record.get("retrieval_priority", "")).strip() != "exclude"]
        selected_papers = usable_papers[:MAX_RETRIEVAL_PAPERS]
        if not selected_papers:
            selected_papers = [record for _, record in scored_papers[:1]]

    selected_source_urls = {
        str(record.get("source_url", "")).strip()
        for record in selected_papers
        if str(record.get("source_url", "")).strip()
    }
    source_metadata_by_url: dict[str, dict[str, Any]] = {}
    if isinstance(raw_paper_cache, list):
        for raw_record in raw_paper_cache:
            if not isinstance(raw_record, dict):
                continue
            source_url = str(raw_record.get("source_url", "")).strip()
            if not source_url:
                continue
            source_metadata_by_url[source_url] = {
                "source_kind": str(raw_record.get("source_kind", "")).strip(),
                "retrieval_priority": str(raw_record.get("retrieval_priority", "")).strip(),
                "direct_reading_access": str(raw_record.get("direct_reading_access", "")).strip(),
                "download_relpath": str(raw_record.get("download_relpath", "")).strip(),
                "download_path": str(raw_record.get("download_path", "")).strip(),
                "paper_record_relpath": str(raw_record.get("paper_record_relpath", "")).strip(),
                "paper_record_path": str(raw_record.get("paper_record_path", "")).strip(),
            }
    source_link_entries = payload.get("source_link_entries", [])
    compact_source_link_entries = (
        _select_retrieval_source_link_entries(query_term_set, source_link_entries, selected_source_urls, source_metadata_by_url)
        if isinstance(source_link_entries, list)
        else []
    )
    compact_source_links = [
        " - ".join(part for part in (entry["label"], entry["url"]) if part).strip()
        for entry in compact_source_link_entries
    ]
    if not compact_source_links:
        raw_source_links = payload.get("source_links", [])
        if isinstance(raw_source_links, list):
            compact_source_links = [str(item).strip() for item in raw_source_links[:MAX_RETRIEVAL_SOURCE_LINKS] if str(item).strip()]

    compact_materials: dict[str, Any] = {
        "materials_dir": str(payload.get("materials_dir", "")).strip(),
        "materials_cache_dir": str(payload.get("materials_cache_dir", "")).strip(),
        "notes": [str(item).strip() for item in payload.get("notes", []) if str(item).strip()][:4]
        if isinstance(payload.get("notes", []), list)
        else [],
        "problem_generation": [str(item).strip() for item in payload.get("problem_generation", []) if str(item).strip()][:6]
        if isinstance(payload.get("problem_generation", []), list)
        else [],
        "problem_evaluation": [str(item).strip() for item in payload.get("problem_evaluation", []) if str(item).strip()][:6]
        if isinstance(payload.get("problem_evaluation", []), list)
        else [],
        "main_theorem": [str(item).strip() for item in payload.get("main_theorem", []) if str(item).strip()][:MAX_RETRIEVAL_MAIN_THEOREM_NOTES]
        if isinstance(payload.get("main_theorem", []), list)
        else [],
        "source_links": compact_source_links,
        "source_link_entries": compact_source_link_entries,
        "documents": _select_retrieval_documents(query_term_set, payload.get("documents", []))
        if isinstance(payload.get("documents", []), list)
        else [],
        "paper_cache": selected_papers,
        "paper_excerpt_context": [
            {
                "reference": str(record.get("title", "")).strip() or str(record.get("source_id", "")).strip(),
                "source_url": str(record.get("source_url", "")).strip(),
                "extract_confidence": str(record.get("extract_confidence", "")).strip(),
                "source_kind": str(record.get("source_kind", "")).strip(),
                "retrieval_priority": str(record.get("retrieval_priority", "")).strip(),
                "direct_reading_access": str(record.get("direct_reading_access", "")).strip(),
                "relevance_score": int(record.get("relevance_score", 0) or 0),
                "paper_record_relpath": str(record.get("paper_record_relpath", "")).strip(),
                "paper_record_path": str(record.get("paper_record_path", "")).strip(),
                "download_relpath": str(record.get("download_relpath", "")).strip(),
                "download_path": str(record.get("download_path", "")).strip(),
                "abstract_excerpt": str(record.get("abstract", "")).strip(),
                "selected_chunks": [
                    {
                        "chunk_id": str(chunk.get("chunk_id", "")).strip(),
                        "section": str(chunk.get("section", "")).strip(),
                        "text": str(chunk.get("text", "")).strip(),
                    }
                    for chunk in record.get("chunks", [])
                    if isinstance(chunk, dict)
                ],
            }
            for record in selected_papers
        ],
        "retrieval_query_terms": query_terms,
    }
    return compact_materials


def _validate_main_theorem_candidate(
    raw_candidate: dict[str, Any],
    *,
    known_problem_id_set: set[str],
    candidate_index: int,
) -> dict[str, Any]:
    required_keys = {
        "candidate_rank_seed",
        "statement",
        "theorem_name_stem",
        "docstring_summary",
        "rationale",
        "supporting_theorems",
        "missing_lemmas",
        "source_problem_ids",
        "theorem_pattern",
        "context_note",
        "conceptual_depth_note",
    }
    if set(raw_candidate.keys()) != required_keys:
        raise ValueError(f"main_theorem candidate {candidate_index} keys mismatch required contract")

    candidate_rank_seed = raw_candidate.get("candidate_rank_seed")
    if not isinstance(candidate_rank_seed, int):
        raise ValueError(f"main_theorem candidate {candidate_index} candidate_rank_seed must be an integer")

    statement = str(raw_candidate.get("statement", "")).strip()
    theorem_name_stem = validate_theorem_name_stem(str(raw_candidate.get("theorem_name_stem", "")).strip())
    docstring_summary = str(raw_candidate.get("docstring_summary", "")).strip()
    rationale = str(raw_candidate.get("rationale", "")).strip()
    theorem_pattern = str(raw_candidate.get("theorem_pattern", "")).strip()
    context_note = str(raw_candidate.get("context_note", "")).strip()
    conceptual_depth_note = str(raw_candidate.get("conceptual_depth_note", "")).strip()
    supporting_value = raw_candidate.get("supporting_theorems", [])
    missing_value = raw_candidate.get("missing_lemmas", [])
    source_problem_ids_value = raw_candidate.get("source_problem_ids", [])
    if not isinstance(supporting_value, list) or not isinstance(missing_value, list) or not isinstance(source_problem_ids_value, list):
        raise ValueError(
            f"main_theorem candidate {candidate_index} supporting_theorems, missing_lemmas, and source_problem_ids must be arrays"
        )

    supporting_theorems = [str(item).strip() for item in supporting_value if str(item).strip()]
    missing_lemmas = [str(item).strip() for item in missing_value if str(item).strip()]
    source_problem_ids: list[str] = []
    seen_source_ids: set[str] = set()
    for item in source_problem_ids_value:
        problem_id = str(item).strip()
        if not problem_id or problem_id in seen_source_ids:
            continue
        if known_problem_id_set and problem_id not in known_problem_id_set:
            raise ValueError(f"main_theorem candidate {candidate_index} source_problem_id is not in tracked_problems: {problem_id}")
        seen_source_ids.add(problem_id)
        source_problem_ids.append(problem_id)

    if not statement:
        raise ValueError(f"main_theorem candidate {candidate_index} statement must be non-empty")
    if not docstring_summary:
        raise ValueError(f"main_theorem candidate {candidate_index} docstring_summary must be non-empty")
    if not rationale:
        raise ValueError(f"main_theorem candidate {candidate_index} rationale must be non-empty")
    if known_problem_id_set and not source_problem_ids:
        raise ValueError(f"main_theorem candidate {candidate_index} source_problem_ids must be non-empty")
    if theorem_pattern not in MAIN_THEOREM_PATTERNS:
        raise ValueError(
            "main_theorem candidate theorem_pattern must be new_theorem|structure_discovery|framework_introduction"
        )
    if not context_note:
        raise ValueError(f"main_theorem candidate {candidate_index} context_note must be non-empty")
    if not conceptual_depth_note:
        raise ValueError(f"main_theorem candidate {candidate_index} conceptual_depth_note must be non-empty")

    return {
        "candidate_rank_seed": candidate_rank_seed,
        "statement": statement,
        "theorem_name_stem": theorem_name_stem,
        "docstring_summary": docstring_summary,
        "rationale": rationale,
        "supporting_theorems": supporting_theorems,
        "missing_lemmas": missing_lemmas,
        "source_problem_ids": source_problem_ids,
        "theorem_pattern": theorem_pattern,
        "context_note": context_note,
        "conceptual_depth_note": conceptual_depth_note,
    }


def validate_main_theorem_candidate_set_output(
    payload: dict[str, Any],
    expected_candidate_set_id: str,
    known_problem_ids: list[str],
) -> list[dict[str, Any]]:
    required_keys = {"candidate_set_id", "candidates"}
    if set(payload.keys()) != required_keys:
        raise ValueError("main_theorem_generate output keys mismatch required contract")

    candidate_set_id = str(payload.get("candidate_set_id", "")).strip()
    if candidate_set_id != expected_candidate_set_id:
        raise ValueError("main_theorem_generate candidate_set_id does not match request")

    raw_candidates = payload.get("candidates", [])
    if not isinstance(raw_candidates, list):
        raise ValueError("main_theorem_generate candidates must be an array")
    if len(raw_candidates) != MAIN_THEOREM_CANDIDATE_COUNT:
        raise ValueError(f"main_theorem_generate must return exactly {MAIN_THEOREM_CANDIDATE_COUNT} candidates")

    known_problem_id_set = {str(item).strip() for item in known_problem_ids if str(item).strip()}
    normalized_candidates: list[dict[str, Any]] = []
    seen_rank_seeds: set[int] = set()
    seen_statement_norms: set[str] = set()
    seen_theorem_name_stems: set[str] = set()
    theorem_patterns: set[str] = set()
    for candidate_index, item in enumerate(raw_candidates, start=1):
        if not isinstance(item, dict):
            raise ValueError("main_theorem_generate candidates must contain only objects")
        candidate = _validate_main_theorem_candidate(
            item,
            known_problem_id_set=known_problem_id_set,
            candidate_index=candidate_index,
        )
        candidate_rank_seed = int(candidate["candidate_rank_seed"])
        if candidate_rank_seed < 1 or candidate_rank_seed > MAIN_THEOREM_CANDIDATE_COUNT:
            raise ValueError("main_theorem_generate candidate_rank_seed must be within the fixed candidate set")
        if candidate_rank_seed in seen_rank_seeds:
            raise ValueError("main_theorem_generate candidate_rank_seed values must be unique")
        seen_rank_seeds.add(candidate_rank_seed)

        statement_norm = " ".join(str(candidate["statement"]).split()).lower()
        if statement_norm in seen_statement_norms:
            raise ValueError("main_theorem_generate candidate statements must be distinct")
        seen_statement_norms.add(statement_norm)

        theorem_name_stem = str(candidate["theorem_name_stem"])
        if theorem_name_stem in seen_theorem_name_stems:
            raise ValueError("main_theorem_generate theorem_name_stem values must be unique")
        seen_theorem_name_stems.add(theorem_name_stem)

        theorem_patterns.add(str(candidate["theorem_pattern"]))
        normalized_candidates.append(candidate)

    if seen_rank_seeds != set(range(1, MAIN_THEOREM_CANDIDATE_COUNT + 1)):
        raise ValueError("main_theorem_generate candidate_rank_seed values must cover the fixed candidate set")
    if len(theorem_patterns) < 2:
        raise ValueError("main_theorem_generate candidate set must contain at least two distinct theorem patterns")

    return sorted(normalized_candidates, key=lambda item: int(item["candidate_rank_seed"]))


def validate_main_theorem_selection_output(
    payload: dict[str, Any],
    *,
    expected_candidate_set_id: str,
    candidates: list[dict[str, Any]],
) -> tuple[int, str, list[dict[str, Any]]]:
    required_keys = {"candidate_set_id", "selected_candidate_rank_seed", "selection_summary", "ranking"}
    if set(payload.keys()) != required_keys:
        raise ValueError("main_theorem_select output keys mismatch required contract")

    candidate_set_id = str(payload.get("candidate_set_id", "")).strip()
    if candidate_set_id != expected_candidate_set_id:
        raise ValueError("main_theorem_select candidate_set_id does not match request")

    selected_candidate_rank_seed = payload.get("selected_candidate_rank_seed")
    if not isinstance(selected_candidate_rank_seed, int):
        raise ValueError("main_theorem_select selected_candidate_rank_seed must be an integer")

    selection_summary = str(payload.get("selection_summary", "")).strip()
    if not selection_summary:
        raise ValueError("main_theorem_select selection_summary must be non-empty")

    ranking_value = payload.get("ranking", [])
    if not isinstance(ranking_value, list):
        raise ValueError("main_theorem_select ranking must be an array")
    if len(ranking_value) != len(candidates):
        raise ValueError("main_theorem_select ranking length must match candidate count")

    candidate_rank_seed_set = {int(candidate["candidate_rank_seed"]) for candidate in candidates}
    normalized_ranking: list[dict[str, Any]] = []
    seen_candidate_rank_seeds: set[int] = set()
    seen_ranks: set[int] = set()
    selected_entries = 0
    for item in ranking_value:
        if not isinstance(item, dict):
            raise ValueError("main_theorem_select ranking entries must be objects")
        if set(item.keys()) != {"candidate_rank_seed", "rank", "decision", "reason"}:
            raise ValueError("main_theorem_select ranking entry keys mismatch required contract")

        candidate_rank_seed = item.get("candidate_rank_seed")
        rank = item.get("rank")
        if not isinstance(candidate_rank_seed, int) or not isinstance(rank, int):
            raise ValueError("main_theorem_select ranking candidate_rank_seed and rank must be integers")
        decision = str(item.get("decision", "")).strip()
        reason = str(item.get("reason", "")).strip()
        if candidate_rank_seed not in candidate_rank_seed_set:
            raise ValueError("main_theorem_select ranking candidate_rank_seed must refer to an input candidate")
        if candidate_rank_seed in seen_candidate_rank_seeds:
            raise ValueError("main_theorem_select ranking candidate_rank_seed values must be unique")
        if rank < 1 or rank > len(candidates):
            raise ValueError("main_theorem_select ranking rank is out of bounds")
        if rank in seen_ranks:
            raise ValueError("main_theorem_select ranking rank values must be unique")
        if decision not in {"select", "reject"}:
            raise ValueError("main_theorem_select decision must be select or reject")
        if not reason:
            raise ValueError("main_theorem_select reason must be non-empty")
        if decision == "select":
            selected_entries += 1

        seen_candidate_rank_seeds.add(candidate_rank_seed)
        seen_ranks.add(rank)
        normalized_ranking.append(
            {
                "candidate_rank_seed": candidate_rank_seed,
                "rank": rank,
                "decision": decision,
                "reason": reason,
            }
        )

    if seen_candidate_rank_seeds != candidate_rank_seed_set:
        raise ValueError("main_theorem_select ranking must cover each input candidate exactly once")
    if seen_ranks != set(range(1, len(candidates) + 1)):
        raise ValueError("main_theorem_select ranking must cover every rank exactly once")
    if selected_entries != 1:
        raise ValueError("main_theorem_select must mark exactly one candidate as select")
    if selected_candidate_rank_seed not in candidate_rank_seed_set:
        raise ValueError("main_theorem_select selected_candidate_rank_seed must refer to an input candidate")

    ranking_by_rank = {int(item["rank"]): item for item in normalized_ranking}
    top_entry = ranking_by_rank[1]
    if int(top_entry["candidate_rank_seed"]) != selected_candidate_rank_seed or str(top_entry["decision"]) != "select":
        raise ValueError("main_theorem_select rank 1 must be the selected candidate")
    for rank in range(2, len(candidates) + 1):
        if str(ranking_by_rank[rank]["decision"]) != "reject":
            raise ValueError("main_theorem_select ranks below 1 must be rejected")

    return selected_candidate_rank_seed, selection_summary, sorted(normalized_ranking, key=lambda item: int(item["rank"]))


def validate_main_theorem_suggestion_output(
    payload: dict[str, Any],
    *,
    expected_candidate_id: str,
    known_problem_ids: list[str],
) -> dict[str, Any]:
    required_keys = {
        "candidate_id",
        "result",
        "statement",
        "theorem_name_stem",
        "docstring_summary",
        "rationale",
        "supporting_theorems",
        "missing_lemmas",
        "source_problem_ids",
        "theorem_pattern",
        "context_note",
        "conceptual_depth_note",
    }
    if set(payload.keys()) != required_keys:
        raise ValueError("main_theorem_suggest output keys mismatch required contract")

    candidate_id = str(payload.get("candidate_id", "")).strip()
    if candidate_id != expected_candidate_id:
        raise ValueError("main_theorem_suggest candidate_id does not match request")
    if str(payload.get("result", "")).strip() != "ok":
        raise ValueError("main_theorem_suggest result must be ok")

    candidate = _validate_main_theorem_candidate(
        {
            "candidate_rank_seed": 1,
            "statement": payload.get("statement", ""),
            "theorem_name_stem": payload.get("theorem_name_stem", ""),
            "docstring_summary": payload.get("docstring_summary", ""),
            "rationale": payload.get("rationale", ""),
            "supporting_theorems": payload.get("supporting_theorems", []),
            "missing_lemmas": payload.get("missing_lemmas", []),
            "source_problem_ids": payload.get("source_problem_ids", []),
            "theorem_pattern": payload.get("theorem_pattern", ""),
            "context_note": payload.get("context_note", ""),
            "conceptual_depth_note": payload.get("conceptual_depth_note", ""),
        },
        known_problem_id_set={str(item).strip() for item in known_problem_ids if str(item).strip()},
        candidate_index=1,
    )
    candidate["candidate_id"] = candidate_id
    return candidate


def validate_main_theorem_retrieval_output(
    payload: dict[str, Any],
    *,
    expected_candidate_id: str,
) -> dict[str, Any]:
    required_keys = {
        "candidate_id",
        "closest_items",
        "research_line",
        "coverage_assessment",
        "missing_angles",
        "need_supplemental_retrieval",
    }
    if set(payload.keys()) != required_keys:
        raise ValueError("main_theorem_retrieve output keys mismatch required contract")

    candidate_id = str(payload.get("candidate_id", "")).strip()
    if candidate_id != expected_candidate_id:
        raise ValueError("main_theorem_retrieve candidate_id does not match request")

    closest_items_value = payload.get("closest_items", [])
    if not isinstance(closest_items_value, list):
        raise ValueError("main_theorem_retrieve closest_items must be an array")
    normalized_items: list[dict[str, Any]] = []
    for item_index, item in enumerate(closest_items_value, start=1):
        if not isinstance(item, dict):
            raise ValueError("main_theorem_retrieve closest_items must contain only objects")
        if set(item.keys()) != {"reference", "kind", "relevance", "confidence"}:
            raise ValueError(f"main_theorem_retrieve closest_item {item_index} keys mismatch required contract")
        reference = str(item.get("reference", "")).strip()
        kind = str(item.get("kind", "")).strip()
        relevance = str(item.get("relevance", "")).strip()
        confidence = str(item.get("confidence", "")).strip()
        if not reference or not kind or not relevance:
            raise ValueError(f"main_theorem_retrieve closest_item {item_index} fields must be non-empty")
        if confidence not in {"high", "medium", "low"}:
            raise ValueError("main_theorem_retrieve closest_item confidence must be high|medium|low")
        normalized_items.append(
            {
                "reference": reference,
                "kind": kind,
                "relevance": relevance,
                "confidence": confidence,
            }
        )

    missing_angles_value = payload.get("missing_angles", [])
    if not isinstance(missing_angles_value, list):
        raise ValueError("main_theorem_retrieve missing_angles must be an array")
    missing_angles = [str(item).strip() for item in missing_angles_value if str(item).strip()]

    research_line = str(payload.get("research_line", "")).strip()
    coverage_assessment = str(payload.get("coverage_assessment", "")).strip()
    need_supplemental_retrieval = payload.get("need_supplemental_retrieval")
    if not research_line or not coverage_assessment:
        raise ValueError("main_theorem_retrieve research_line and coverage_assessment must be non-empty")
    if not isinstance(need_supplemental_retrieval, bool):
        raise ValueError("main_theorem_retrieve need_supplemental_retrieval must be a boolean")

    return {
        "candidate_id": candidate_id,
        "closest_items": normalized_items,
        "research_line": research_line,
        "coverage_assessment": coverage_assessment,
        "missing_angles": missing_angles,
        "need_supplemental_retrieval": need_supplemental_retrieval,
    }


def validate_main_theorem_mapping_output(
    payload: dict[str, Any],
    *,
    expected_candidate_id: str,
) -> dict[str, Any]:
    required_keys = {
        "candidate_id",
        "closest_baseline",
        "relations",
        "overall_novelty_risk",
        "variant_objection",
    }
    if set(payload.keys()) != required_keys:
        raise ValueError("main_theorem_map output keys mismatch required contract")

    candidate_id = str(payload.get("candidate_id", "")).strip()
    if candidate_id != expected_candidate_id:
        raise ValueError("main_theorem_map candidate_id does not match request")

    relations_value = payload.get("relations", [])
    if not isinstance(relations_value, list):
        raise ValueError("main_theorem_map relations must be an array")
    relations: list[dict[str, Any]] = []
    for relation_index, item in enumerate(relations_value, start=1):
        if not isinstance(item, dict):
            raise ValueError("main_theorem_map relations must contain only objects")
        if set(item.keys()) != {"reference", "overlap", "delta", "delta_materiality"}:
            raise ValueError(f"main_theorem_map relation {relation_index} keys mismatch required contract")
        reference = str(item.get("reference", "")).strip()
        overlap = str(item.get("overlap", "")).strip()
        delta = str(item.get("delta", "")).strip()
        delta_materiality = str(item.get("delta_materiality", "")).strip()
        if not reference or not overlap or not delta:
            raise ValueError(f"main_theorem_map relation {relation_index} fields must be non-empty")
        if delta_materiality not in {"substantial", "unclear", "minor"}:
            raise ValueError("main_theorem_map delta_materiality must be substantial|unclear|minor")
        relations.append(
            {
                "reference": reference,
                "overlap": overlap,
                "delta": delta,
                "delta_materiality": delta_materiality,
            }
        )

    closest_baseline = str(payload.get("closest_baseline", "")).strip()
    overall_novelty_risk = str(payload.get("overall_novelty_risk", "")).strip()
    variant_objection = str(payload.get("variant_objection", "")).strip()
    if not closest_baseline or not variant_objection:
        raise ValueError("main_theorem_map closest_baseline and variant_objection must be non-empty")
    if overall_novelty_risk not in {"high", "medium", "low"}:
        raise ValueError("main_theorem_map overall_novelty_risk must be high|medium|low")

    return {
        "candidate_id": candidate_id,
        "closest_baseline": closest_baseline,
        "relations": relations,
        "overall_novelty_risk": overall_novelty_risk,
        "variant_objection": variant_objection,
    }


def validate_main_theorem_evaluation_output(
    payload: dict[str, Any],
    *,
    expected_candidate_id: str,
) -> dict[str, Any]:
    required_keys = {
        "candidate_id",
        "novelty",
        "significance",
        "paper_unit_viability",
        "strongest_objection",
        "objection_answerable",
        "minimal_publishable_unit",
        "salvage_plan",
        "verdict",
        "reason",
    }
    if set(payload.keys()) != required_keys:
        raise ValueError("main_theorem_evaluate output keys mismatch required contract")

    candidate_id = str(payload.get("candidate_id", "")).strip()
    if candidate_id != expected_candidate_id:
        raise ValueError("main_theorem_evaluate candidate_id does not match request")

    novelty = str(payload.get("novelty", "")).strip()
    significance = str(payload.get("significance", "")).strip()
    paper_unit_viability = str(payload.get("paper_unit_viability", "")).strip()
    strongest_objection = str(payload.get("strongest_objection", "")).strip()
    objection_answerable = str(payload.get("objection_answerable", "")).strip()
    minimal_publishable_unit = str(payload.get("minimal_publishable_unit", "")).strip()
    salvage_plan = str(payload.get("salvage_plan", "")).strip()
    verdict = str(payload.get("verdict", "")).strip()
    reason = str(payload.get("reason", "")).strip()

    if novelty not in {"high", "medium", "low"}:
        raise ValueError("main_theorem_evaluate novelty must be high|medium|low")
    if significance not in {"high", "medium", "low"}:
        raise ValueError("main_theorem_evaluate significance must be high|medium|low")
    if paper_unit_viability not in {"yes", "borderline", "no"}:
        raise ValueError("main_theorem_evaluate paper_unit_viability must be yes|borderline|no")
    if objection_answerable not in {"yes", "partial", "no"}:
        raise ValueError("main_theorem_evaluate objection_answerable must be yes|partial|no")
    if verdict not in {"pass", "revise", "reject"}:
        raise ValueError("main_theorem_evaluate verdict must be pass|revise|reject")
    if not strongest_objection or not minimal_publishable_unit or not reason:
        raise ValueError("main_theorem_evaluate strongest_objection, minimal_publishable_unit, and reason must be non-empty")

    return {
        "candidate_id": candidate_id,
        "novelty": novelty,
        "significance": significance,
        "paper_unit_viability": paper_unit_viability,
        "strongest_objection": strongest_objection,
        "objection_answerable": objection_answerable,
        "minimal_publishable_unit": minimal_publishable_unit,
        "salvage_plan": salvage_plan,
        "verdict": verdict,
        "reason": reason,
    }


def request_main_theorem_suggestion(
    *,
    worker_settings: Any,
    suggester_prompt: str,
    candidate_id: str,
    derived_entries: list[dict[str, str]],
    theory_context: str,
    tracked_rows: list[dict[str, Any]],
    current_iteration: int,
    guidance: dict[str, Any],
    rejected_candidates: list[dict[str, Any]],
    attempt_index: int,
) -> tuple[dict[str, Any], dict[str, Any]]:
    tracked_problem_payload, known_problem_ids = _build_main_theorem_tracked_problem_payload(tracked_rows)
    theory_state, research_agenda, materials = unpack_guidance_context(guidance)
    payload: dict[str, Any] = {
        "candidate_id": candidate_id,
        "attempt_index": attempt_index,
        "current_iteration": current_iteration,
        "derived_theorems": [
            {
                "name": str(entry.get("name", "")),
                "statement": str(entry.get("statement", "")),
            }
            for entry in derived_entries
        ],
        "theory_context": theory_context,
        "tracked_problems": tracked_problem_payload,
        "rejected_candidates": rejected_candidates,
        "theory_state": theory_state,
        "research_agenda": research_agenda,
        "materials": materials,
    }
    response, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="main_theorem_suggest",
        system_prompt=suggester_prompt,
        payload=payload,
        metadata={"candidate_id": candidate_id, "derived_theorem_count": len(derived_entries)},
    )
    return validate_main_theorem_suggestion_output(
        response,
        expected_candidate_id=candidate_id,
        known_problem_ids=known_problem_ids,
    ), worker_meta


def request_main_theorem_retrieval(
    *,
    worker_settings: Any,
    retriever_prompt: str,
    candidate: dict[str, Any],
    derived_entries: list[dict[str, str]],
    theory_context: str,
    tracked_rows: list[dict[str, Any]],
    current_iteration: int,
    guidance: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    tracked_problem_payload, _ = _build_main_theorem_tracked_problem_payload(tracked_rows)
    theory_state, research_agenda, materials = unpack_guidance_context(guidance)
    retrieval_materials = _build_main_theorem_retrieval_materials(candidate, materials)
    payload: dict[str, Any] = {
        "candidate_id": str(candidate["candidate_id"]),
        "current_iteration": current_iteration,
        "candidate": candidate,
        "derived_theorems": [
            {
                "name": str(entry.get("name", "")),
                "statement": str(entry.get("statement", "")),
            }
            for entry in derived_entries
        ],
        "theory_context": theory_context,
        "tracked_problems": tracked_problem_payload,
        "theory_state": theory_state,
        "research_agenda": research_agenda,
        "materials": retrieval_materials,
    }
    response, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="main_theorem_retrieve",
        system_prompt=retriever_prompt,
        payload=payload,
        metadata={
            "candidate_id": str(candidate["candidate_id"]),
            "paper_excerpt_count": len(retrieval_materials.get("paper_excerpt_context", [])),
        },
    )
    return validate_main_theorem_retrieval_output(response, expected_candidate_id=str(candidate["candidate_id"])), worker_meta


def request_main_theorem_mapping(
    *,
    worker_settings: Any,
    mapper_prompt: str,
    candidate: dict[str, Any],
    retrieval: dict[str, Any],
    current_iteration: int,
    guidance: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    theory_state, research_agenda, materials = unpack_guidance_context(guidance)
    review_materials = _build_main_theorem_retrieval_materials(candidate, materials)
    payload: dict[str, Any] = {
        "candidate_id": str(candidate["candidate_id"]),
        "current_iteration": current_iteration,
        "candidate": candidate,
        "retrieval": retrieval,
        "theory_state": theory_state,
        "research_agenda": research_agenda,
        "materials": review_materials,
    }
    response, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="main_theorem_map",
        system_prompt=mapper_prompt,
        payload=payload,
        metadata={
            "candidate_id": str(candidate["candidate_id"]),
            "paper_excerpt_count": len(review_materials.get("paper_excerpt_context", [])),
        },
    )
    return validate_main_theorem_mapping_output(response, expected_candidate_id=str(candidate["candidate_id"])), worker_meta


def request_main_theorem_evaluation(
    *,
    worker_settings: Any,
    evaluator_prompt: str,
    candidate: dict[str, Any],
    retrieval: dict[str, Any],
    mapping: dict[str, Any],
    current_iteration: int,
    guidance: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    theory_state, research_agenda, materials = unpack_guidance_context(guidance)
    review_materials = _build_main_theorem_retrieval_materials(candidate, materials)
    payload: dict[str, Any] = {
        "candidate_id": str(candidate["candidate_id"]),
        "current_iteration": current_iteration,
        "candidate": candidate,
        "retrieval": retrieval,
        "mapping": mapping,
        "theory_state": theory_state,
        "research_agenda": research_agenda,
        "materials": review_materials,
    }
    response, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="main_theorem_evaluate",
        system_prompt=evaluator_prompt,
        payload=payload,
        metadata={
            "candidate_id": str(candidate["candidate_id"]),
            "paper_excerpt_count": len(review_materials.get("paper_excerpt_context", [])),
        },
    )
    return validate_main_theorem_evaluation_output(response, expected_candidate_id=str(candidate["candidate_id"])), worker_meta


def request_main_theorem_candidate_set(
    *,
    worker_settings: Any,
    generator_prompt: str,
    candidate_set_id: str,
    derived_entries: list[dict[str, str]],
    theory_context: str,
    tracked_rows: list[dict[str, Any]],
    current_iteration: int,
    guidance: dict[str, Any],
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    tracked_problem_payload, known_problem_ids = _build_main_theorem_tracked_problem_payload(tracked_rows)
    theory_state, research_agenda, materials = unpack_guidance_context(guidance)
    payload: dict[str, Any] = {
        "candidate_set_id": candidate_set_id,
        "candidate_count": MAIN_THEOREM_CANDIDATE_COUNT,
        "current_iteration": current_iteration,
        "derived_theorems": [
            {
                "name": str(entry.get("name", "")),
                "statement": str(entry.get("statement", "")),
            }
            for entry in derived_entries
        ],
        "theory_context": theory_context,
        "tracked_problems": tracked_problem_payload,
        "theory_state": theory_state,
        "research_agenda": research_agenda,
        "materials": materials,
    }
    response, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="main_theorem_generate",
        system_prompt=generator_prompt,
        payload=payload,
        metadata={"candidate_set_id": candidate_set_id, "derived_theorem_count": len(derived_entries)},
    )
    return validate_main_theorem_candidate_set_output(response, candidate_set_id, known_problem_ids), worker_meta


def request_main_theorem_selection(
    *,
    worker_settings: Any,
    selector_prompt: str,
    candidate_set_id: str,
    candidates: list[dict[str, Any]],
    derived_entries: list[dict[str, str]],
    theory_context: str,
    tracked_rows: list[dict[str, Any]],
    current_iteration: int,
    guidance: dict[str, Any],
) -> tuple[tuple[int, str, list[dict[str, Any]]], dict[str, Any]]:
    tracked_problem_payload, _ = _build_main_theorem_tracked_problem_payload(tracked_rows)
    theory_state, research_agenda, materials = unpack_guidance_context(guidance)
    payload: dict[str, Any] = {
        "candidate_set_id": candidate_set_id,
        "current_iteration": current_iteration,
        "candidates": candidates,
        "derived_theorems": [
            {
                "name": str(entry.get("name", "")),
                "statement": str(entry.get("statement", "")),
            }
            for entry in derived_entries
        ],
        "theory_context": theory_context,
        "tracked_problems": tracked_problem_payload,
        "theory_state": theory_state,
        "research_agenda": research_agenda,
        "materials": materials,
    }
    response, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="main_theorem_select",
        system_prompt=selector_prompt,
        payload=payload,
        metadata={"candidate_set_id": candidate_set_id, "candidate_count": len(candidates)},
    )
    return (
        validate_main_theorem_selection_output(
            response,
            expected_candidate_set_id=candidate_set_id,
            candidates=candidates,
        ),
        worker_meta,
    )


def run_main_theorem_session(
    *,
    worker_settings: Any,
    scratch_file: Path,
    derived_file: Path,
    derived_entries: list[dict[str, str]],
    data_dir: Path,
    base_theory_context: str,
    formalization_memory_path: Path,
    formalize_worker_settings: Any,
    repair_worker_settings: Any,
    formalizer_prompt_file: str,
    repair_prompt_file: str,
    suggester_prompt_file: str,
    retriever_prompt_file: str,
    mapper_prompt_file: str,
    evaluator_prompt_file: str,
    post_expand_prompt_file: str,
    prioritize_open_problems_worker_settings: Any,
    prioritize_open_problems_prompt_file: str,
    theory_file: Path,
    repo_root: Path,
    batch_generator_seed_count: int,
    batch_generator_open_target_min: int,
    current_iteration: int,
    skip_verify: bool,
    verify_timeout_sec: int | None,
    formalization_retry_budget_sec: int | None,
    main_theorem_retry_budget_sec: int | None,
    max_same_error_streak: int,
    failure_threshold: int,
    phase_logs: bool,
    run_id: str,
    phase_attempts_path: Path | None,
    session_events_path: Path | None,
    compile_metrics: dict[str, Any],
    state_lock: threading.Lock,
    derived_runtime_state: dict[str, Any],
) -> dict[str, Any]:
    suggester_prompt = load_prompt_text(suggester_prompt_file)
    retriever_prompt = load_prompt_text(retriever_prompt_file)
    mapper_prompt = load_prompt_text(mapper_prompt_file)
    evaluator_prompt = load_prompt_text(evaluator_prompt_file)
    materials_sync_report: dict[str, Any] | None = None
    try:
        materials_sync_report = ensure_materials_cache_current(
            repo_root / "materials",
            fetch_missing=True,
            extract_downloads=True,
        )
    except Exception:
        materials_sync_report = None
    open_rows = [normalize_open_problem_row(row) for row in read_jsonl(data_dir / "open_problems.jsonl")]
    archived_rows = read_archived_problem_rows(data_dir)
    tracked_rows = [dict(row, queue_status="open") for row in open_rows]
    tracked_rows.extend(dict(row, queue_status="archived") for row in archived_rows)
    guidance = load_current_guidance(data_dir)
    rejection_memory_path = data_dir / MAIN_THEOREM_REJECTION_MEMORY_FILENAME
    rejection_history = load_main_theorem_rejection_memory(rejection_memory_path)
    visible_rejections = _build_main_theorem_rejected_candidate_payload(rejection_history)
    search_budget_sec = main_theorem_retry_budget_sec
    if search_budget_sec is None:
        search_budget_sec = formalization_retry_budget_sec if formalization_retry_budget_sec is not None else 900
    search_deadline = time.monotonic() + max(1, int(search_budget_sec))

    accepted_candidate: dict[str, Any] | None = None
    accepted_retrieval: dict[str, Any] | None = None
    accepted_mapping: dict[str, Any] | None = None
    accepted_evaluation: dict[str, Any] | None = None
    failed_stage = ""
    failed_error = ""
    rejected_this_session: list[dict[str, Any]] = []

    for attempt_index in range(1, MAX_MAIN_THEOREM_REJECTION_ATTEMPTS + 1):
        if time.monotonic() > search_deadline:
            break

        candidate_id = f"mt_main_theorem_{attempt_index:02d}"
        emit_phase_log(
            phase_logs,
            "main_theorem_suggest",
            iteration=current_iteration,
            candidate_id=candidate_id,
            attempt_index=attempt_index,
            derived_theorem_count=len(derived_entries),
            open_problem_count=len(open_rows),
            tracked_problem_count=len(tracked_rows),
            visible_rejected_candidate_count=len(visible_rejections),
        )
        suggest_started_monotonic = time.monotonic()
        suggest_started_at = iso_timestamp_now()
        try:
            candidate, _ = request_main_theorem_suggestion(
                worker_settings=worker_settings,
                suggester_prompt=suggester_prompt,
                candidate_id=candidate_id,
                derived_entries=derived_entries,
                theory_context=base_theory_context,
                tracked_rows=tracked_rows,
                current_iteration=current_iteration,
                guidance=guidance,
                rejected_candidates=visible_rejections,
                attempt_index=attempt_index,
            )
        except (RuntimeError, ValueError) as exc:
            failed_stage = "main_theorem_suggest"
            failed_error = str(exc)
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type="main_theorem_session",
                iteration=current_iteration,
                entity_id=candidate_id,
                phase="main_theorem_suggest",
                worker_task="main_theorem_suggest",
                started_at=suggest_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(suggest_started_monotonic),
                success=False,
                result="error",
                error=failed_error,
            )
            emit_phase_log(
                phase_logs,
                "main_theorem_suggest_result",
                iteration=current_iteration,
                candidate_id=candidate_id,
                status="error",
                error=failed_error,
            )
            _append_main_theorem_session_event(
                session_events_path,
                event="main_theorem_suggest_result",
                run_id=run_id,
                iteration=current_iteration,
                candidate_set_id=candidate_id,
                payload={"status": "error", "error": failed_error},
            )
            break
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type="main_theorem_session",
            iteration=current_iteration,
            entity_id=candidate_id,
            phase="main_theorem_suggest",
            worker_task="main_theorem_suggest",
            started_at=suggest_started_at,
            finished_at=iso_timestamp_now(),
            duration_ms=monotonic_duration_ms(suggest_started_monotonic),
            success=True,
            result="ok",
        )
        emit_phase_log(
            phase_logs,
            "main_theorem_suggest_result",
            iteration=current_iteration,
            candidate_id=candidate_id,
            status="ok",
            theorem_name_stem=str(candidate["theorem_name_stem"]),
            statement=str(candidate["statement"]),
            theorem_pattern=str(candidate["theorem_pattern"]),
        )
        _append_main_theorem_session_event(
            session_events_path,
            event="main_theorem_suggest_result",
            run_id=run_id,
            iteration=current_iteration,
            candidate_set_id=candidate_id,
            payload={
                "status": "ok",
                "candidate": {
                    "theorem_name_stem": str(candidate["theorem_name_stem"]),
                    "statement": str(candidate["statement"]),
                    "theorem_pattern": str(candidate["theorem_pattern"]),
                },
            },
        )

        emit_phase_log(
            phase_logs,
            "main_theorem_retrieve",
            iteration=current_iteration,
            candidate_id=candidate_id,
            attempt_index=attempt_index,
        )
        _, _, retrieval_source_materials = unpack_guidance_context(guidance)
        retrieval_access_summary = _summarize_retrieval_source_access(
            _build_main_theorem_retrieval_materials(candidate, retrieval_source_materials)
        )
        retrieve_started_monotonic = time.monotonic()
        retrieve_started_at = iso_timestamp_now()
        try:
            retrieval, _ = request_main_theorem_retrieval(
                worker_settings=worker_settings,
                retriever_prompt=retriever_prompt,
                candidate=candidate,
                derived_entries=derived_entries,
                theory_context=base_theory_context,
                tracked_rows=tracked_rows,
                current_iteration=current_iteration,
                guidance=guidance,
            )
        except (RuntimeError, ValueError) as exc:
            failed_stage = "main_theorem_retrieve"
            failed_error = str(exc)
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type="main_theorem_session",
                iteration=current_iteration,
                entity_id=candidate_id,
                phase="main_theorem_retrieve",
                worker_task="main_theorem_retrieve",
                started_at=retrieve_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(retrieve_started_monotonic),
                success=False,
                result="error",
                error=failed_error,
            )
            emit_phase_log(
                phase_logs,
                "main_theorem_retrieve_result",
                iteration=current_iteration,
                candidate_id=candidate_id,
                status="error",
                error=failed_error,
            )
            _append_main_theorem_session_event(
                session_events_path,
                event="main_theorem_retrieve_result",
                run_id=run_id,
                iteration=current_iteration,
                candidate_set_id=candidate_id,
                payload={"status": "error", "error": failed_error},
            )
            break
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type="main_theorem_session",
            iteration=current_iteration,
            entity_id=candidate_id,
            phase="main_theorem_retrieve",
            worker_task="main_theorem_retrieve",
            started_at=retrieve_started_at,
            finished_at=iso_timestamp_now(),
            duration_ms=monotonic_duration_ms(retrieve_started_monotonic),
            success=True,
            result="ok",
        )
        emit_phase_log(
            phase_logs,
            "main_theorem_retrieve_result",
            iteration=current_iteration,
            candidate_id=candidate_id,
            status="ok",
            closest_item_count=len(retrieval["closest_items"]),
            need_supplemental_retrieval=bool(retrieval["need_supplemental_retrieval"]),
            local_paper_access_count=len(retrieval_access_summary["paper_access"]),
            local_source_link_access_count=len(retrieval_access_summary["source_link_access"]),
        )
        _append_main_theorem_session_event(
            session_events_path,
            event="main_theorem_retrieve_result",
            run_id=run_id,
            iteration=current_iteration,
            candidate_set_id=candidate_id,
            payload={
                "status": "ok",
                "closest_items": list(retrieval["closest_items"]),
                "research_line": str(retrieval["research_line"]),
                "coverage_assessment": str(retrieval["coverage_assessment"]),
                "need_supplemental_retrieval": bool(retrieval["need_supplemental_retrieval"]),
                "source_access": retrieval_access_summary,
            },
        )

        emit_phase_log(
            phase_logs,
            "main_theorem_map",
            iteration=current_iteration,
            candidate_id=candidate_id,
            attempt_index=attempt_index,
        )
        map_started_monotonic = time.monotonic()
        map_started_at = iso_timestamp_now()
        try:
            mapping, _ = request_main_theorem_mapping(
                worker_settings=worker_settings,
                mapper_prompt=mapper_prompt,
                candidate=candidate,
                retrieval=retrieval,
                current_iteration=current_iteration,
                guidance=guidance,
            )
        except (RuntimeError, ValueError) as exc:
            failed_stage = "main_theorem_map"
            failed_error = str(exc)
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type="main_theorem_session",
                iteration=current_iteration,
                entity_id=candidate_id,
                phase="main_theorem_map",
                worker_task="main_theorem_map",
                started_at=map_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(map_started_monotonic),
                success=False,
                result="error",
                error=failed_error,
            )
            emit_phase_log(
                phase_logs,
                "main_theorem_map_result",
                iteration=current_iteration,
                candidate_id=candidate_id,
                status="error",
                error=failed_error,
            )
            _append_main_theorem_session_event(
                session_events_path,
                event="main_theorem_map_result",
                run_id=run_id,
                iteration=current_iteration,
                candidate_set_id=candidate_id,
                payload={"status": "error", "error": failed_error},
            )
            break
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type="main_theorem_session",
            iteration=current_iteration,
            entity_id=candidate_id,
            phase="main_theorem_map",
            worker_task="main_theorem_map",
            started_at=map_started_at,
            finished_at=iso_timestamp_now(),
            duration_ms=monotonic_duration_ms(map_started_monotonic),
            success=True,
            result="ok",
        )
        emit_phase_log(
            phase_logs,
            "main_theorem_map_result",
            iteration=current_iteration,
            candidate_id=candidate_id,
            status="ok",
            relation_count=len(mapping["relations"]),
            overall_novelty_risk=str(mapping["overall_novelty_risk"]),
        )
        _append_main_theorem_session_event(
            session_events_path,
            event="main_theorem_map_result",
            run_id=run_id,
            iteration=current_iteration,
            candidate_set_id=candidate_id,
            payload={
                "status": "ok",
                "closest_baseline": str(mapping["closest_baseline"]),
                "relations": list(mapping["relations"]),
                "overall_novelty_risk": str(mapping["overall_novelty_risk"]),
                "variant_objection": str(mapping["variant_objection"]),
            },
        )

        emit_phase_log(
            phase_logs,
            "main_theorem_evaluate",
            iteration=current_iteration,
            candidate_id=candidate_id,
            attempt_index=attempt_index,
        )
        evaluate_started_monotonic = time.monotonic()
        evaluate_started_at = iso_timestamp_now()
        try:
            evaluation, _ = request_main_theorem_evaluation(
                worker_settings=worker_settings,
                evaluator_prompt=evaluator_prompt,
                candidate=candidate,
                retrieval=retrieval,
                mapping=mapping,
                current_iteration=current_iteration,
                guidance=guidance,
            )
        except (RuntimeError, ValueError) as exc:
            failed_stage = "main_theorem_evaluate"
            failed_error = str(exc)
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type="main_theorem_session",
                iteration=current_iteration,
                entity_id=candidate_id,
                phase="main_theorem_evaluate",
                worker_task="main_theorem_evaluate",
                started_at=evaluate_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(evaluate_started_monotonic),
                success=False,
                result="error",
                error=failed_error,
            )
            emit_phase_log(
                phase_logs,
                "main_theorem_evaluate_result",
                iteration=current_iteration,
                candidate_id=candidate_id,
                status="error",
                error=failed_error,
            )
            _append_main_theorem_session_event(
                session_events_path,
                event="main_theorem_evaluate_result",
                run_id=run_id,
                iteration=current_iteration,
                candidate_set_id=candidate_id,
                payload={"status": "error", "error": failed_error},
            )
            break
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type="main_theorem_session",
            iteration=current_iteration,
            entity_id=candidate_id,
            phase="main_theorem_evaluate",
            worker_task="main_theorem_evaluate",
            started_at=evaluate_started_at,
            finished_at=iso_timestamp_now(),
            duration_ms=monotonic_duration_ms(evaluate_started_monotonic),
            success=True,
            result="ok",
        )
        emit_phase_log(
            phase_logs,
            "main_theorem_evaluate_result",
            iteration=current_iteration,
            candidate_id=candidate_id,
            status="ok",
            verdict=str(evaluation["verdict"]),
            novelty=str(evaluation["novelty"]),
            significance=str(evaluation["significance"]),
            paper_unit_viability=str(evaluation["paper_unit_viability"]),
        )
        _append_main_theorem_session_event(
            session_events_path,
            event="main_theorem_evaluate_result",
            run_id=run_id,
            iteration=current_iteration,
            candidate_set_id=candidate_id,
            payload={"status": "ok", **evaluation},
        )

        if str(evaluation["verdict"]) == "pass":
            accepted_candidate = candidate
            accepted_retrieval = retrieval
            accepted_mapping = mapping
            accepted_evaluation = evaluation
            break

        rejection_entry = {
            "candidate_id": candidate_id,
            "statement": str(candidate["statement"]),
            "theorem_name_stem": str(candidate["theorem_name_stem"]),
            "rationale": str(candidate["rationale"]),
            "verdict": str(evaluation["verdict"]),
            "reason": str(evaluation["reason"]),
            "strongest_objection": str(evaluation["strongest_objection"]),
            "salvage_plan": str(evaluation["salvage_plan"]),
            "paper_unit_viability": str(evaluation["paper_unit_viability"]),
            "novelty": str(evaluation["novelty"]),
            "significance": str(evaluation["significance"]),
            "iteration": current_iteration,
        }
        rejection_history = append_main_theorem_rejection_entry(rejection_memory_path, rejection_entry)
        visible_rejections = _build_main_theorem_rejected_candidate_payload(rejection_history)
        rejected_this_session.append(rejection_entry)
        emit_phase_log(
            phase_logs,
            "main_theorem_reject_and_retry",
            iteration=current_iteration,
            candidate_id=candidate_id,
            verdict=str(evaluation["verdict"]),
            reason=str(evaluation["reason"]),
            rejection_count=len(rejected_this_session),
        )

    if accepted_candidate is None or accepted_retrieval is None or accepted_mapping is None or accepted_evaluation is None:
        status = "main_theorem_rejected_all"
        if failed_stage:
            status = f"{failed_stage}_error"
        return {
            "status": status,
            "processed": False,
            "verify_success": False,
            "error": failed_error,
            "rejected_candidates": rejected_this_session,
            "rejection_count": len(rejected_this_session),
            "generated_candidates": [],
            "selected_candidate_rank_seed": None,
            "selection_summary": "",
            "ranking": [],
        }

    report = process_main_theorem(
        candidate_id=str(accepted_candidate["candidate_id"]),
        statement=str(accepted_candidate["statement"]),
        theorem_name=f"main_thm_{accepted_candidate['theorem_name_stem']}",
        docstring_summary=str(accepted_candidate["docstring_summary"]),
        rationale=str(accepted_candidate["rationale"]),
        supporting_theorems=list(accepted_candidate["supporting_theorems"]),
        missing_lemmas=list(accepted_candidate["missing_lemmas"]),
        scratch_file=scratch_file,
        derived_file=derived_file,
        derived_entries=derived_entries,
        data_dir=data_dir,
        base_theory_context=base_theory_context,
        formalization_memory_path=formalization_memory_path,
        formalize_worker_settings=formalize_worker_settings,
        repair_worker_settings=repair_worker_settings,
        worker_settings=worker_settings,
        formalizer_prompt_file=formalizer_prompt_file,
        repair_prompt_file=repair_prompt_file,
        post_expand_prompt_file=post_expand_prompt_file,
        prioritize_open_problems_worker_settings=prioritize_open_problems_worker_settings,
        prioritize_open_problems_prompt_file=prioritize_open_problems_prompt_file,
        theory_file=theory_file,
        repo_root=repo_root,
        batch_generator_seed_count=batch_generator_seed_count,
        batch_generator_open_target_min=batch_generator_open_target_min,
        current_iteration=current_iteration,
        skip_verify=skip_verify,
        verify_timeout_sec=verify_timeout_sec,
        formalization_retry_budget_sec=formalization_retry_budget_sec,
        max_same_error_streak=max_same_error_streak,
        failure_threshold=failure_threshold,
        phase_logs=phase_logs,
        run_id=run_id,
        phase_attempts_path=phase_attempts_path,
        theory_state_history_path=(
            (phase_attempts_path.parent if phase_attempts_path is not None else data_dir)
            / "theory_state_history.jsonl"
        ),
        compile_metrics=compile_metrics,
        state_lock=state_lock,
        derived_runtime_state=derived_runtime_state,
    )
    report["generated_candidates"] = [accepted_candidate]
    report["selected_candidate_rank_seed"] = 1
    report["selection_summary"] = str(accepted_evaluation["reason"])
    report["ranking"] = [
        {
            "candidate_rank_seed": 1,
            "rank": 1,
            "decision": "select",
            "reason": str(accepted_evaluation["reason"]),
        }
    ]
    report["suggested_statement"] = str(accepted_candidate["statement"])
    report["suggested_rationale"] = str(accepted_candidate["rationale"])
    report["source_problem_ids"] = list(accepted_candidate["source_problem_ids"])
    report["retrieval"] = accepted_retrieval
    report["mapping"] = accepted_mapping
    report["evaluation"] = accepted_evaluation
    report["rejected_candidates"] = rejected_this_session
    report["rejection_count"] = len(rejected_this_session)
    if materials_sync_report is not None:
        report["materials_sync"] = materials_sync_report
    if session_events_path is not None:
        report["session_events_file"] = str(session_events_path)
    return report


def process_main_theorem(
    *,
    candidate_id: str,
    statement: str,
    theorem_name: str,
    docstring_summary: str,
    rationale: str,
    supporting_theorems: list[str],
    missing_lemmas: list[str],
    scratch_file: Path,
    derived_file: Path,
    derived_entries: list[dict[str, str]],
    data_dir: Path,
    base_theory_context: str,
    formalization_memory_path: Path,
    formalize_worker_settings: Any,
    repair_worker_settings: Any,
    worker_settings: Any,
    formalizer_prompt_file: str,
    repair_prompt_file: str,
    post_expand_prompt_file: str,
    prioritize_open_problems_worker_settings: Any,
    prioritize_open_problems_prompt_file: str,
    theory_file: Path,
    repo_root: Path,
    batch_generator_seed_count: int,
    batch_generator_open_target_min: int,
    current_iteration: int,
    skip_verify: bool,
    verify_timeout_sec: int | None,
    formalization_retry_budget_sec: int | None,
    max_same_error_streak: int,
    failure_threshold: int,
    phase_logs: bool,
    run_id: str,
    phase_attempts_path: Path | None,
    theory_state_history_path: Path,
    compile_metrics: dict[str, Any],
    state_lock: threading.Lock,
    derived_runtime_state: dict[str, Any],
) -> dict[str, Any]:
    statement = statement.strip()
    theorem_name = theorem_name.strip()
    if not statement or not theorem_name:
        return {
            "processed": False,
            "candidate_id": candidate_id,
            "status": "blocked",
            "verify_success": False,
        }

    scratch_file.parent.mkdir(parents=True, exist_ok=True)
    scratch_file.write_text(SCRATCH_TEMPLATE, encoding="utf-8")

    theorem_context = build_problem_theory_context(base_theory_context, derived_entries, statement)
    current_iteration_full_logs: list[dict[str, Any]] = []
    intermediate_lemmas: list[str] = []
    proof_sketch = rationale.strip() or f"Prove {theorem_name} from the current Derived.lean cluster."

    proof_formalizer_prompt = load_prompt_text(formalizer_prompt_file)
    proof_repair_prompt = load_prompt_text(repair_prompt_file)
    verify_success, _, result, _, _, _, verify_error_excerpt, final_stmt = attempt_formalization_until_timeout(
        problem_id=candidate_id,
        theorem_name=theorem_name,
        stmt=statement,
        result="proof",
        proof_sketch=proof_sketch,
        counterexample_text="",
        scratch_file=scratch_file,
        skip_verify=skip_verify,
        formalize_worker_settings=formalize_worker_settings,
        repair_worker_settings=repair_worker_settings,
        formalizer_prompts={"proof": proof_formalizer_prompt, "counterexample": proof_formalizer_prompt},
        repair_prompts={"proof": proof_repair_prompt, "counterexample": proof_repair_prompt},
        open_rows=[normalize_open_problem_row(row) for row in read_jsonl(data_dir / "open_problems.jsonl")],
        theory_context=theorem_context,
        verify_timeout_sec=verify_timeout_sec,
        formalization_retry_budget_sec=formalization_retry_budget_sec,
        memory_path=formalization_memory_path,
        current_iteration_full_logs=current_iteration_full_logs,
        initial_proof_text="",
        phase_logger=(lambda **fields: emit_phase_log(phase_logs, iteration=current_iteration, **fields)),
        forbid_sorry=True,
        max_same_error_streak=max_same_error_streak,
        retry_initial_formalization_until_budget=True,
        run_id=run_id,
        session_type="main_theorem_session",
        iteration=current_iteration,
        phase_attempts_path=phase_attempts_path,
        compile_metrics=compile_metrics,
    )
    emit_phase_log(
        phase_logs,
        "main_theorem_formalization_result",
        iteration=current_iteration,
        candidate_id=candidate_id,
        theorem_name=theorem_name,
        result=result,
        verify_success=verify_success,
        error_excerpt=verify_error_excerpt,
    )

    if not is_verified_resolution(verify_success=verify_success, result=result):
        followup_refresh = _store_main_theorem_followups(
            data_dir=data_dir,
            theorem_name=theorem_name,
            statement=final_stmt.strip() or statement,
            rationale=rationale,
            verify_error_excerpt=verify_error_excerpt,
            missing_lemmas=missing_lemmas,
            intermediate_lemmas=intermediate_lemmas,
            prioritize_open_problems_worker_settings=prioritize_open_problems_worker_settings,
            prioritize_open_problems_prompt_file=prioritize_open_problems_prompt_file,
            derived_entries=derived_entries,
            current_iteration=current_iteration,
            failure_threshold=failure_threshold,
            run_id=run_id,
            theory_state_history_path=theory_state_history_path,
            theory_file=theory_file,
            derived_file=derived_file,
            repo_root=repo_root,
            batch_generator_seed_count=batch_generator_seed_count,
            batch_generator_open_target_min=batch_generator_open_target_min,
        )
        return {
            "processed": True,
            "candidate_id": candidate_id,
            "status": "blocked",
            "verify_success": False,
            "verify_error_excerpt": verify_error_excerpt,
            "followup_candidates": list(followup_refresh.get("followup_candidates", [])),
            "stored_expand_rows": list(followup_refresh.get("stored_expand_rows", [])),
            "priority_refresh_ran": bool(followup_refresh.get("priority_refresh_ran", False)),
            "priority_refresh_error": str(followup_refresh.get("priority_refresh_error", "")),
        }

    theorem_code = extract_theorem_code_from_scratch(scratch_file)
    derived_entries_for_context = [dict(entry) for entry in derived_entries]
    if theorem_code:
        append_derived_entry_cache(derived_entries_for_context, theorem_code)
    emit_phase_log(
        phase_logs,
        "main_theorem_append_derived",
        iteration=current_iteration,
        candidate_id=candidate_id,
        theorem_name=theorem_name,
        appended=bool(theorem_code),
    )
    known_theorem_names = {
        str(entry.get("name", "")).strip()
        for entry in derived_entries_for_context
        if str(entry.get("name", "")).strip()
    }

    post_expand_candidates: list[dict[str, str]] = []
    post_expand_error = ""
    theorem_context = build_problem_theory_context(base_theory_context, derived_entries_for_context, final_stmt)
    if theorem_code:
        emit_phase_log(
            phase_logs,
            "post_theorem_expand",
            iteration=current_iteration,
            candidate_id=candidate_id,
            theorem_name=theorem_name,
        )
        post_expand_started_monotonic = time.monotonic()
        post_expand_started_at = iso_timestamp_now()
        try:
            post_expand_candidates, _ = request_expand_candidates(
                worker_settings=worker_settings,
                expand_prompt=load_prompt_text(post_expand_prompt_file),
                task_type="post_theorem_expand",
                problem_id=candidate_id,
                stmt=final_stmt,
                original_stmt=statement,
                result=result,
                verify_success=verify_success,
                theory_context=theorem_context,
                open_rows=[normalize_open_problem_row(row) for row in read_jsonl(data_dir / "open_problems.jsonl")],
                existing_new_problems=[],
                verify_error_excerpt="",
                current_iteration_full_logs=current_iteration_full_logs,
                same_problem_history_tail=load_formalization_memory(formalization_memory_path, candidate_id)[-8:],
                theory_state=load_theory_state(data_dir),
                max_candidates=MAX_EXPAND_CANDIDATES_PER_MAIN_THEOREM,
            )
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type="main_theorem_session",
                iteration=current_iteration,
                entity_id=candidate_id,
                phase="post_theorem_expand",
                worker_task="post_theorem_expand",
                started_at=post_expand_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(post_expand_started_monotonic),
                success=True,
                result="ok",
            )
            emit_phase_log(
                phase_logs,
                "post_theorem_expand_result",
                iteration=current_iteration,
                candidate_id=candidate_id,
                generated_problem_count=len(post_expand_candidates),
            )
        except (RuntimeError, ValueError) as exc:
            post_expand_error = str(exc)
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type="main_theorem_session",
                iteration=current_iteration,
                entity_id=candidate_id,
                phase="post_theorem_expand",
                worker_task="post_theorem_expand",
                started_at=post_expand_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(post_expand_started_monotonic),
                success=False,
                result="error",
                error=post_expand_error,
            )
            emit_phase_log(
                phase_logs,
                "post_theorem_expand_result",
                iteration=current_iteration,
                candidate_id=candidate_id,
                status="error",
                error=post_expand_error,
            )

    theorem_reuse_payload = {
        "candidate_id": candidate_id,
        "theorem_name": theorem_name,
        "statement": final_stmt.strip() or statement,
        "docstring_summary": docstring_summary,
        "rationale": rationale,
        "supporting_theorems": [theorem for theorem in supporting_theorems if theorem in known_theorem_names],
        "intermediate_lemmas": intermediate_lemmas,
        "iteration": current_iteration,
        "appended_to_derived": bool(theorem_code),
    }
    with state_lock:
        committed_theorem_code = commit_verified_theorem_and_generation(
            scratch_path=scratch_file,
            derived_file=derived_file,
            derived_entries=derived_entries,
            docstring=docstring_summary,
            data_dir=data_dir,
            derived_runtime_state=derived_runtime_state,
            run_id=run_id,
            current_iteration=current_iteration,
            rebuild_derived=not skip_verify,
        )
        theorem_reuse_payload["appended_to_derived"] = bool(committed_theorem_code)
        append_theorem_reuse_memory_entry(data_dir / "theorem_reuse_memory.json", theorem_reuse_payload)
        refresh_outcome = store_expand_candidates_and_refresh(
            data_dir=data_dir,
            statements_with_rationale=post_expand_candidates,
            source="post_theorem_expand",
            source_problem_id=theorem_name,
            source_kind="main_theorem",
            prioritize_worker_settings=prioritize_open_problems_worker_settings,
            prioritizer_prompt_file=prioritize_open_problems_prompt_file,
            derived_entries=derived_entries,
            current_iteration=current_iteration,
            failure_threshold=failure_threshold,
            run_id=run_id,
            theory_state_history_path=theory_state_history_path,
            theory_file=theory_file,
            derived_file=derived_file,
            repo_root=repo_root,
            batch_generator_seed_count=batch_generator_seed_count,
            batch_generator_open_target_min=batch_generator_open_target_min,
            allow_backfill=False,
        )
        stored_expand_rows = list(refresh_outcome.get("stored_expand_rows", []))
        priority_refresh_ran = bool(refresh_outcome.get("priority_refresh_ran", False))
        priority_refresh_error = str(refresh_outcome.get("priority_refresh_error", ""))
        priority_refresh_report = dict(refresh_outcome.get("priority_refresh_report", {}))
        if bool(refresh_outcome.get("priority_refresh_failed", False)):
            return {
                "processed": True,
                "candidate_id": candidate_id,
                "status": "proved",
                "verify_success": True,
                "theorem_name": theorem_name,
                "statement": final_stmt.strip() or statement,
                "theorem_code": committed_theorem_code,
                "supporting_theorems": list(supporting_theorems),
                "post_theorem_expand_candidates": post_expand_candidates,
                "stored_expand_rows": stored_expand_rows,
                "post_theorem_expand_error": post_expand_error,
                "batch_generator_added_problem_rows": list(priority_refresh_report.get("batch_generator_added_problem_rows", [])),
                "batch_generator_error": str(priority_refresh_report.get("batch_generator_error", "")),
                "promoted_expand_rows": [],
                "priority_refresh_ran": False,
                "priority_refresh_error": priority_refresh_error,
            }
    return {
        "processed": True,
        "candidate_id": candidate_id,
        "status": "proved",
        "verify_success": True,
        "theorem_name": theorem_name,
        "statement": final_stmt.strip() or statement,
        "theorem_code": committed_theorem_code,
        "supporting_theorems": list(supporting_theorems),
        "post_theorem_expand_candidates": post_expand_candidates,
        "stored_expand_rows": stored_expand_rows,
        "post_theorem_expand_error": post_expand_error,
        "batch_generator_added_problem_rows": list(priority_refresh_report.get("batch_generator_added_problem_rows", [])) if priority_refresh_ran else [],
        "batch_generator_error": str(priority_refresh_report.get("batch_generator_error", "")) if priority_refresh_ran else "",
        "promoted_expand_rows": list(priority_refresh_report.get("worker_meta", {}).get("promoted_expand_rows", [])) if priority_refresh_ran else [],
        "priority_refresh_ran": priority_refresh_ran,
        "priority_refresh_error": priority_refresh_error,
    }
