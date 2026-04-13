from __future__ import annotations

import json
import re
import sys
import tempfile
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

from atc_paths import loop_open_problems_path
from atc_paths import loop_theorem_reuse_memory_path
from atc_paths import paper_claim_run_dir
from common import append_jsonl
from common import read_jsonl
from common import normalize_open_problem_row
from derived_entries import extract_derived_theorem_entries
from generated_library import render_scratch_template
from guidance import unpack_guidance_context
from lean_verify import verify_scratch
from loop_common import iso_timestamp_now
from loop_common import monotonic_duration_ms
from loop_helpers import append_derived_entry_cache
from loop_helpers import append_phase_attempt_record
from loop_helpers import build_problem_theory_context
from loop_helpers import emit_phase_log
from loop_helpers import extract_theorem_code_from_scratch
from loop_helpers import load_current_guidance
from loop_helpers import load_theory_state
from loop_helpers import shortlist_relevant_derived_entries
from loop_helpers import validate_theorem_name_stem
from problem_expansion import request_expand_candidates
from problem_expansion import store_expand_candidates_and_refresh
from prompt_loader import load_prompt_file
from paper_claim_rejection_memory import append_paper_claim_rejection_entry
from paper_claim_rejection_memory import load_paper_claim_rejection_memory
from materials_sync import ensure_materials_cache_current
from theorem_commit import commit_verified_theorem_and_generation
from theorem_reuse_memory import append_theorem_reuse_memory_entry
from worker_client import invoke_worker_json


SCRATCH_TEMPLATE = render_scratch_template()
MAX_EXPAND_CANDIDATES_PER_PAPER_CLAIM = 5
PAPER_CLAIM_CANDIDATE_COUNT = 3
PAPER_CLAIM_PATTERNS = {"new_theorem", "structure_discovery", "framework_introduction"}
PAPER_CLAIM_REJECTION_TAGS = {
    "minor_variant",
    "weak_novelty",
    "too_local",
    "not_paper_unit",
    "needs_stronger_baseline_delta",
    "needs_scope_shift",
    "missing_framework_claim",
    "missing_boundary_claim",
}
PAPER_CLAIM_REJECTION_MEMORY_FILENAME = "paper_claim_rejection_memory.json"
MAX_PAPER_CLAIM_REJECTION_ATTEMPTS = 20
MAX_VISIBLE_REJECTED_CANDIDATES = 12
MAX_RETRIEVAL_QUERY_TERMS = 32
MAX_RETRIEVAL_SOURCE_LINKS = 8
MAX_RETRIEVAL_DOCUMENTS = 8
MAX_RETRIEVAL_PAPER_CLAIM_NOTES = 6
MAX_RETRIEVAL_PAPERS = 4
MAX_RETRIEVAL_PAPER_CHUNKS = 3
MAX_RETRIEVAL_READING_PAPERS = 3
MAX_RETRIEVAL_READING_CHUNKS = 5
MAX_RETRIEVAL_CHUNK_CHARS = 500
MAX_PROBLEM_DESIGN_CLUSTERS = 4
PAPER_CLAIM_CONCEPTUAL_THEORY_STATE_LIST_KEYS = {
    "important_verified_counterexamples",
    "desired_summary_changes",
    "current_bottlenecks",
    "overexplored_patterns",
    "missing_bridges",
}
PROBLEM_DESIGN_KINDS = {
    "semantic_equivalence",
    "algorithmic_characterization",
    "boundary_or_sharpness",
    "canonicality",
    "framework_consequence",
}
PROBLEM_DESIGN_BOUNDARY_HINTS = {
    "boundary",
    "intrinsic_invariant",
    "impossibility",
    "classifier",
    "universality",
}
PROBLEM_DESIGN_DELTA_TYPES = {
    "new_equivalence",
    "algorithmic_reading",
    "canonicality",
    "bound_interpretation",
    "scope_shift_only",
}
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
WEAK_DIRECT_READING_ACCESS = {
    "",
    "blocked",
    "discussion",
    "image_only_pdf",
    "landing_page",
    "metadata_only",
    "unclear",
}


def load_prompt_text(prompt_file: str) -> str:
    return load_prompt_file(Path(prompt_file))


def _build_paper_claim_followup_candidates(
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


def _summarize_paper_claim_candidates(candidates: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "candidate_rank_seed": int(candidate["candidate_rank_seed"]),
            "theorem_name_stem": str(candidate["theorem_name_stem"]),
            "statement": str(candidate["statement"]),
            "theorem_pattern": str(candidate["theorem_pattern"]),
        }
        for candidate in candidates
    ]


def _summarize_paper_claim_ranking(
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


def _append_paper_claim_session_event(
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
    event_payload = {
        "event": event,
        "run_id": run_id,
        "recorded_at": iso_timestamp_now(),
        **payload,
    }
    redundant_ids = {
        str(payload.get("problem_id", "")).strip(),
        str(payload.get("cluster_id", "")).strip(),
        str(payload.get("selection_id", "")).strip(),
        str(payload.get("plan_id", "")).strip(),
        str(payload.get("candidate_id", "")).strip(),
    }
    candidate_set_id = str(candidate_set_id).strip()
    if candidate_set_id and candidate_set_id not in redundant_ids:
        event_payload["candidate_set_id"] = candidate_set_id
    append_jsonl(
        session_events_path,
        event_payload,
    )


def _store_paper_claim_followups(
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
    followup_candidates = _build_paper_claim_followup_candidates(
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
        source="paper_claim_followup",
        source_problem_id=theorem_name,
        source_kind="paper_claim",
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


def _latest_paper_claim_event(
    rows: list[dict[str, Any]],
    *,
    event: str,
    end_index: int | None = None,
    predicate: Any | None = None,
) -> tuple[int, dict[str, Any] | None]:
    limit = len(rows) if end_index is None else max(0, min(end_index, len(rows)))
    for index in range(limit - 1, -1, -1):
        row = rows[index]
        if str(row.get("event", "")).strip() != event:
            continue
        if predicate is not None and not bool(predicate(row)):
            continue
        return index, row
    return -1, None


def _extract_resume_paper_claim_plan(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "plan_id": str(row.get("plan_id", "")).strip(),
        "selected_problem_id": str(row.get("selected_problem_id", "")).strip(),
        "headline": str(row.get("headline", "")).strip(),
        "package_strategy": str(row.get("package_strategy", "")).strip(),
        "theorem_units": list(row.get("theorem_units", [])),
        "formalization_order": list(row.get("formalization_order", [])),
    }


def load_paper_claim_resume_context_from_session_events(
    *,
    session_events_path: Path,
    plan_id: str = "",
) -> dict[str, Any]:
    rows = [row for row in read_jsonl(session_events_path) if isinstance(row, dict)]
    if not rows:
        raise ValueError(f"resume session events file is empty: {session_events_path}")

    normalized_plan_id = str(plan_id).strip()
    plan_index, plan_row = _latest_paper_claim_event(
        rows,
        event="paper_claim_plan_result",
        predicate=lambda row: (
            str(row.get("status", "")).strip() == "ok"
            and (
                not normalized_plan_id
                or str(row.get("plan_id", "")).strip() == normalized_plan_id
                or str(row.get("candidate_set_id", "")).strip() == normalized_plan_id
            )
        ),
    )
    if plan_row is None:
        wanted = f" for plan_id={normalized_plan_id}" if normalized_plan_id else ""
        raise ValueError(f"could not find an ok paper_claim_plan_result{wanted} in {session_events_path}")

    paper_claim_plan = _extract_resume_paper_claim_plan(plan_row)
    validate_paper_claim_plan_output(
        paper_claim_plan,
        expected_plan_id=str(paper_claim_plan.get("plan_id", "")).strip(),
        known_problem_ids=[str(paper_claim_plan.get("selected_problem_id", "")).strip()],
    )
    selected_problem_id = str(paper_claim_plan["selected_problem_id"]).strip()

    selection_payload = plan_row.get("paper_claim_selection")
    if isinstance(selection_payload, dict) and str(selection_payload.get("selected_problem_id", "")).strip() == selected_problem_id:
        paper_claim_selection = dict(selection_payload)
    else:
        _, selection_row = _latest_paper_claim_event(
            rows,
            event="paper_claim_select_result",
            end_index=plan_index,
            predicate=lambda row: (
                str(row.get("status", "")).strip() == "ok"
                and str(row.get("selected_problem_id", "")).strip() == selected_problem_id
            ),
        )
        if selection_row is None:
            raise ValueError("resume session events are missing a matching paper_claim_select_result")
        paper_claim_selection = {
            "selection_id": str(selection_row.get("selection_id", "")).strip(),
            "selected_problem_id": str(selection_row.get("selected_problem_id", "")).strip(),
            "selection_note": str(selection_row.get("selection_note", "")).strip(),
            "planning_focus": str(selection_row.get("planning_focus", "")).strip(),
            "assessments": list(selection_row.get("assessments", [])),
        }

    selected_dossier_payload = plan_row.get("selected_dossier_package")
    if isinstance(selected_dossier_payload, dict) and str(selected_dossier_payload.get("problem_id", "")).strip() == selected_problem_id:
        selected_dossier_package = dict(selected_dossier_payload)
    else:
        _, core_row = _latest_paper_claim_event(
            rows,
            event="problem_design_core_extract_result",
            end_index=plan_index,
            predicate=lambda row: (
                str(row.get("status", "")).strip() == "ok"
                and isinstance(row.get("core_dossier"), dict)
                and (
                    str(row.get("candidate_set_id", "")).strip() == selected_problem_id
                    or str(row.get("core_dossier", {}).get("problem_id", "")).strip() == selected_problem_id
                )
            ),
        )
        if core_row is None:
            raise ValueError("resume session events are missing a matching problem_design_core_extract_result")
        _, retrieval_row = _latest_paper_claim_event(
            rows,
            event="paper_claim_retrieve_result",
            end_index=plan_index,
            predicate=lambda row: (
                str(row.get("status", "")).strip() == "ok"
                and str(row.get("problem_id", "")).strip() == selected_problem_id
            ),
        )
        if retrieval_row is None:
            raise ValueError("resume session events are missing a matching paper_claim_retrieve_result")
        _, mapping_row = _latest_paper_claim_event(
            rows,
            event="paper_claim_map_result",
            end_index=plan_index,
            predicate=lambda row: (
                str(row.get("status", "")).strip() == "ok"
                and str(row.get("problem_id", "")).strip() == selected_problem_id
            ),
        )
        if mapping_row is None:
            raise ValueError("resume session events are missing a matching paper_claim_map_result")
        core_dossier = dict(core_row.get("core_dossier", {}))
        dossier = {
            "problem_id": selected_problem_id,
            "cluster_id": str(core_dossier.get("cluster_id", "")).strip(),
            "cluster_theme": str(core_dossier.get("cluster_theme", "")).strip(),
            "cluster_summary": str(core_dossier.get("cluster_summary", "")).strip(),
            "headline_claim": str(core_dossier.get("headline_claim", "")).strip(),
            "core_mathematical_content": str(core_dossier.get("core_mathematical_content", "")).strip(),
            "literature_context": dict(core_dossier.get("literature_context", {})),
            "supporting_claims": list(core_dossier.get("supporting_claims", [])),
            "no_go_faces": list(core_dossier.get("no_go_faces", [])),
            "proof_assets": list(core_dossier.get("proof_assets", [])),
            "why_this_face": str(core_dossier.get("why_this_face", "")).strip(),
        }
        selected_dossier_package = {
            "problem_id": selected_problem_id,
            "dossier": dossier,
            "retrieval": {
                "problem_id": str(retrieval_row.get("problem_id", "")).strip(),
                "closest_items": list(retrieval_row.get("closest_items", [])),
                "directly_read_evidence": list(retrieval_row.get("directly_read_evidence", [])),
                "coverage_assessment": str(retrieval_row.get("coverage_assessment", "")).strip(),
                "missing_angles": list(retrieval_row.get("missing_angles", [])),
                "need_supplemental_retrieval": bool(retrieval_row.get("need_supplemental_retrieval", False)),
            },
            "mapping": {
                "problem_id": str(mapping_row.get("problem_id", "")).strip(),
                "closest_baseline": str(mapping_row.get("closest_baseline", "")).strip(),
                "relations": list(mapping_row.get("relations", [])),
                "theorem_face_assessment": str(mapping_row.get("theorem_face_assessment", "")).strip(),
                "baseline_delta": str(mapping_row.get("baseline_delta", "")).strip(),
                "outsider_risk": str(mapping_row.get("outsider_risk", "")).strip(),
            },
        }

    return {
        "paper_claim_plan": paper_claim_plan,
        "paper_claim_selection": paper_claim_selection,
        "selected_dossier_package": selected_dossier_package,
        "selected_problem_id": selected_problem_id,
        "plan_event_iteration": int(plan_row.get("iteration", 0) or 0),
    }


def _build_paper_claim_rejected_candidate_payload(entries: list[dict[str, Any]]) -> list[dict[str, Any]]:
    visible_entries = entries[-MAX_VISIBLE_REJECTED_CANDIDATES:]
    return [
        {
            "candidate_id": str(entry.get("candidate_id", "")),
            "statement": str(entry.get("statement", "")),
            "theorem_name_stem": str(entry.get("theorem_name_stem", "")),
            "rationale": str(entry.get("rationale", "")),
            "verdict": str(entry.get("verdict", "")),
            "reason": str(entry.get("reason", "")),
            "strongest_positive_signal": str(entry.get("strongest_positive_signal", "")),
            "strongest_objection": str(entry.get("strongest_objection", "")),
            "salvage_plan": str(entry.get("salvage_plan", "")),
            "paper_unit_viability": str(entry.get("paper_unit_viability", "")),
            "novelty": str(entry.get("novelty", "")),
            "significance": str(entry.get("significance", "")),
            "rejection_tags": [
                str(tag).strip()
                for tag in entry.get("rejection_tags", [])
                if str(tag).strip()
            ],
            "iteration": int(entry.get("iteration", 0) or 0),
        }
        for entry in visible_entries
    ]


def _build_paper_claim_conceptual_theory_state(theory_state: dict[str, Any]) -> dict[str, Any]:
    if not isinstance(theory_state, dict):
        return {}
    payload: dict[str, Any] = {}
    theory_snapshot = str(theory_state.get("theory_snapshot", "")).strip()
    if theory_snapshot:
        payload["theory_snapshot"] = theory_snapshot
    for key in PAPER_CLAIM_CONCEPTUAL_THEORY_STATE_LIST_KEYS:
        value = theory_state.get(key, [])
        if not isinstance(value, list):
            continue
        if key == "important_verified_counterexamples":
            normalized_rows = [item for item in value if isinstance(item, dict)]
            if normalized_rows:
                payload[key] = normalized_rows
            continue
        normalized_items = [str(item).strip() for item in value if str(item).strip()]
        if normalized_items:
            payload[key] = normalized_items
    return payload


REVIEW_HISTORY_KEYS = {
    "rejected_candidates",
    "required_escape",
    "reuse_allowed_only_if",
    "fatal_baseline_issue",
    "fatal_theorem_face_issue",
    "retained_positive_signal",
    "rejection_count",
}


def _strip_review_history(value: Any) -> Any:
    if isinstance(value, dict):
        return {
            key: _strip_review_history(item)
            for key, item in value.items()
            if key not in REVIEW_HISTORY_KEYS
        }
    if isinstance(value, list):
        return [_strip_review_history(item) for item in value]
    return value


def _looks_like_single_repair_step(text: str) -> bool:
    raw = str(text)
    normalized = " ".join(raw.split()).strip()
    if not normalized:
        return False
    lowered_raw = raw.lower()
    lowered_normalized = normalized.lower()
    return not any(
        marker in lowered_raw or marker in lowered_normalized
        for marker in ("; ", "\n- ", "\n* ", "\n1.", "\n2.", " option ", " options ")
    )


def _json_compact_debug(payload: dict[str, Any]) -> str:
    return json.dumps(payload, ensure_ascii=False, sort_keys=True)


def _build_problem_design_seed_materials(
    theory_state: dict[str, Any],
    materials: dict[str, Any],
) -> dict[str, Any]:
    seed_candidate = {
        "statement": str(theory_state.get("theory_snapshot", "")).strip(),
        "docstring_summary": " ".join(
            str(item).strip()
            for item in theory_state.get("desired_summary_changes", [])
            if str(item).strip()
        ),
        "rationale": " ".join(
            str(item).strip()
            for item in theory_state.get("missing_bridges", [])
            if str(item).strip()
        ),
        "theorem_pattern": "problem_design_seed",
        "context_note": " ".join(
            str(item).strip()
            for item in theory_state.get("current_bottlenecks", [])
            if str(item).strip()
        ),
        "conceptual_depth_note": " ".join(
            str(item).strip()
            for item in theory_state.get("overexplored_patterns", [])
            if str(item).strip()
        ),
        "supporting_theorems": [],
        "missing_lemmas": [],
    }
    return _build_paper_claim_retrieval_materials(seed_candidate, materials)


def _merge_problem_design_inventory_entries(
    derived_entries: list[dict[str, str]],
    derived_file: Path,
) -> list[dict[str, str]]:
    merged_entries: list[dict[str, str]] = []
    seen_keys: set[tuple[str, str]] = set()
    visible_sources = [
        extract_derived_theorem_entries(derived_file),
        [dict(entry) for entry in derived_entries if isinstance(entry, dict)],
    ]
    for source_entries in visible_sources:
        for raw_entry in source_entries:
            name = str(raw_entry.get("name", "")).strip()
            statement = str(raw_entry.get("statement", "")).strip()
            if not name or not statement:
                continue
            dedupe_key = (name, " ".join(statement.split()))
            if dedupe_key in seen_keys:
                continue
            seen_keys.add(dedupe_key)
            merged_entries.append({"name": name, "statement": statement})
    return merged_entries


def _build_problem_design_cluster_materials(
    cluster: dict[str, Any],
    materials: dict[str, Any],
) -> dict[str, Any]:
    proxy_candidate = {
        "statement": " ".join(
            str(item.get("statement", "")).strip()
            for item in cluster.get("member_theorems", [])
            if isinstance(item, dict) and str(item.get("statement", "")).strip()
        ),
        "docstring_summary": str(cluster.get("cluster_theme", "")).strip(),
        "rationale": str(cluster.get("cluster_summary", "")).strip(),
        "theorem_pattern": "problem_design_cluster",
        "context_note": " ".join(
            [
                *[str(item).strip() for item in cluster.get("objects", []) if str(item).strip()],
                *[str(item).strip() for item in cluster.get("invariants", []) if str(item).strip()],
                *[str(item).strip() for item in cluster.get("algorithms", []) if str(item).strip()],
            ]
        ).strip(),
        "conceptual_depth_note": " ".join(
            str(item).strip() for item in cluster.get("suspected_support_layer", []) if str(item).strip()
        ),
        "supporting_theorems": [
            str(item.get("name", "")).strip()
            for item in cluster.get("member_theorems", [])
            if isinstance(item, dict) and str(item.get("name", "")).strip()
        ],
        "missing_lemmas": [],
    }
    return _build_paper_claim_retrieval_materials(proxy_candidate, materials)


def _normalize_problem_design_cluster(cluster: dict[str, Any], *, cluster_index: int) -> dict[str, Any]:
    required_keys = {
        "cluster_id",
        "cluster_theme",
        "cluster_summary",
        "member_theorems",
        "objects",
        "invariants",
        "algorithms",
        "suspected_support_layer",
    }
    if set(cluster.keys()) != required_keys:
        raise ValueError(f"problem_design_cluster cluster {cluster_index} keys mismatch required contract")

    cluster_id = str(cluster.get("cluster_id", "")).strip()
    cluster_theme = str(cluster.get("cluster_theme", "")).strip()
    cluster_summary = str(cluster.get("cluster_summary", "")).strip()
    member_theorems_value = cluster.get("member_theorems", [])
    if not cluster_id or not cluster_theme or not cluster_summary:
        raise ValueError(f"problem_design_cluster cluster {cluster_index} fields must be non-empty")
    if not isinstance(member_theorems_value, list) or not member_theorems_value:
        raise ValueError(f"problem_design_cluster cluster {cluster_index} member_theorems must be a non-empty array")

    member_theorems: list[dict[str, str]] = []
    seen_members: set[tuple[str, str]] = set()
    for theorem_index, raw_member in enumerate(member_theorems_value, start=1):
        if not isinstance(raw_member, dict) or set(raw_member.keys()) != {"name", "statement"}:
            raise ValueError(
                f"problem_design_cluster cluster {cluster_index} member_theorem {theorem_index} keys mismatch required contract"
            )
        theorem_name = str(raw_member.get("name", "")).strip()
        theorem_statement = str(raw_member.get("statement", "")).strip()
        if not theorem_name or not theorem_statement:
            raise ValueError(
                f"problem_design_cluster cluster {cluster_index} member_theorem {theorem_index} fields must be non-empty"
            )
        dedupe_key = (theorem_name, " ".join(theorem_statement.split()))
        if dedupe_key in seen_members:
            continue
        seen_members.add(dedupe_key)
        member_theorems.append({"name": theorem_name, "statement": theorem_statement})
    if not member_theorems:
        raise ValueError(f"problem_design_cluster cluster {cluster_index} must retain at least one member theorem")

    def normalize_str_list(key: str) -> list[str]:
        value = cluster.get(key, [])
        if not isinstance(value, list):
            raise ValueError(f"problem_design_cluster cluster {cluster_index} {key} must be an array")
        normalized: list[str] = []
        for raw_item in value:
            item = str(raw_item).strip()
            if item and item not in normalized:
                normalized.append(item)
        return normalized

    return {
        "cluster_id": cluster_id,
        "cluster_theme": cluster_theme,
        "cluster_summary": cluster_summary,
        "member_theorems": member_theorems,
        "objects": normalize_str_list("objects"),
        "invariants": normalize_str_list("invariants"),
        "algorithms": normalize_str_list("algorithms"),
        "suspected_support_layer": normalize_str_list("suspected_support_layer"),
    }


def _normalize_problem_design_contextualization(payload: dict[str, Any], *, expected_cluster_id: str) -> dict[str, Any]:
    required_keys = {
        "cluster_id",
        "cluster_theme",
        "external_positioning",
        "paper_core_analysis",
        "proposal_guidance",
    }
    if set(payload.keys()) != required_keys:
        raise ValueError("problem_design_contextualize output keys mismatch required contract")

    cluster_id = str(payload.get("cluster_id", "")).strip()
    cluster_theme = str(payload.get("cluster_theme", "")).strip()
    if cluster_id != expected_cluster_id:
        raise ValueError("problem_design_contextualize cluster_id does not match request")
    if not cluster_theme:
        raise ValueError("problem_design_contextualize cluster_theme must be non-empty")

    external_value = payload.get("external_positioning", {})
    paper_core_value = payload.get("paper_core_analysis", {})
    proposal_guidance_value = payload.get("proposal_guidance", {})
    if not all(isinstance(item, dict) for item in (external_value, paper_core_value, proposal_guidance_value)):
        raise ValueError("problem_design_contextualize nested sections must be objects")

    if set(external_value.keys()) != {
        "closest_baselines",
        "baseline_summary",
        "what_counts_as_real_delta",
        "unresolved_baseline_risks",
        "external_baseline_pressure",
    }:
        raise ValueError("problem_design_contextualize external_positioning keys mismatch required contract")
    if set(paper_core_value.keys()) != {
        "no_go_faces",
        "possible_gap_types",
        "most_plausible_gap",
        "gap_rationale",
        "headline_viability",
    }:
        raise ValueError("problem_design_contextualize paper_core_analysis keys mismatch required contract")
    if set(proposal_guidance_value.keys()) != {
        "allowed_headline_directions",
        "discouraged_headline_directions",
        "must_clear_for_novelty",
    }:
        raise ValueError("problem_design_contextualize proposal_guidance keys mismatch required contract")

    def normalize_section_list(value: Any, field_name: str) -> list[str]:
        if not isinstance(value, list):
            raise ValueError(f"problem_design_contextualize {field_name} must be an array")
        normalized: list[str] = []
        for raw_item in value:
            item = str(raw_item).strip()
            if item and item not in normalized:
                normalized.append(item)
        return normalized

    closest_baselines_value = external_value.get("closest_baselines", [])
    if not isinstance(closest_baselines_value, list):
        raise ValueError("problem_design_contextualize closest_baselines must be an array")
    closest_baselines: list[dict[str, str]] = []
    for baseline_index, raw_baseline in enumerate(closest_baselines_value, start=1):
        if not isinstance(raw_baseline, dict) or set(raw_baseline.keys()) != {
            "reference",
            "what_it_already_owns",
            "evidence_strength",
            "danger_level",
        }:
            raise ValueError(
                f"problem_design_contextualize closest_baseline {baseline_index} keys mismatch required contract"
            )
        reference = str(raw_baseline.get("reference", "")).strip()
        what_it_already_owns = str(raw_baseline.get("what_it_already_owns", "")).strip()
        evidence_strength = str(raw_baseline.get("evidence_strength", "")).strip()
        danger_level = str(raw_baseline.get("danger_level", "")).strip()
        if not reference or not what_it_already_owns:
            raise ValueError(f"problem_design_contextualize closest_baseline {baseline_index} fields must be non-empty")
        if evidence_strength not in {"direct", "summary", "weak"}:
            raise ValueError("problem_design_contextualize evidence_strength must be direct|summary|weak")
        if danger_level not in {"high", "medium", "low"}:
            raise ValueError("problem_design_contextualize danger_level must be high|medium|low")
        closest_baselines.append(
            {
                "reference": reference,
                "what_it_already_owns": what_it_already_owns,
                "evidence_strength": evidence_strength,
                "danger_level": danger_level,
            }
        )

    baseline_summary = str(external_value.get("baseline_summary", "")).strip()
    external_baseline_pressure = str(external_value.get("external_baseline_pressure", "")).strip()
    if not baseline_summary:
        raise ValueError("problem_design_contextualize baseline_summary must be non-empty")
    if external_baseline_pressure not in {"high", "medium", "low"}:
        raise ValueError("problem_design_contextualize external_baseline_pressure must be high|medium|low")

    most_plausible_gap = str(paper_core_value.get("most_plausible_gap", "")).strip()
    gap_rationale = str(paper_core_value.get("gap_rationale", "")).strip()
    headline_viability = str(paper_core_value.get("headline_viability", "")).strip()
    if not most_plausible_gap or not gap_rationale:
        raise ValueError("problem_design_contextualize paper_core_analysis fields must be non-empty")
    if headline_viability not in {"promising", "unclear", "weak"}:
        raise ValueError("problem_design_contextualize headline_viability must be promising|unclear|weak")

    return {
        "cluster_id": cluster_id,
        "cluster_theme": cluster_theme,
        "external_positioning": {
            "closest_baselines": closest_baselines,
            "baseline_summary": baseline_summary,
            "what_counts_as_real_delta": normalize_section_list(
                external_value.get("what_counts_as_real_delta", []),
                "what_counts_as_real_delta",
            ),
            "unresolved_baseline_risks": normalize_section_list(
                external_value.get("unresolved_baseline_risks", []),
                "unresolved_baseline_risks",
            ),
            "external_baseline_pressure": external_baseline_pressure,
        },
        "paper_core_analysis": {
            "no_go_faces": normalize_section_list(paper_core_value.get("no_go_faces", []), "no_go_faces"),
            "possible_gap_types": normalize_section_list(
                paper_core_value.get("possible_gap_types", []),
                "possible_gap_types",
            ),
            "most_plausible_gap": most_plausible_gap,
            "gap_rationale": gap_rationale,
            "headline_viability": headline_viability,
        },
        "proposal_guidance": {
            "allowed_headline_directions": normalize_section_list(
                proposal_guidance_value.get("allowed_headline_directions", []),
                "allowed_headline_directions",
            ),
            "discouraged_headline_directions": normalize_section_list(
                proposal_guidance_value.get("discouraged_headline_directions", []),
                "discouraged_headline_directions",
            ),
            "must_clear_for_novelty": normalize_section_list(
                proposal_guidance_value.get("must_clear_for_novelty", []),
                "must_clear_for_novelty",
            ),
        },
    }


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


def _select_retrieval_chunks(
    query_terms: set[str],
    record: dict[str, Any],
    *,
    max_chunks: int = MAX_RETRIEVAL_PAPER_CHUNKS,
) -> list[dict[str, Any]]:
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
    selected = positive_chunks[:max_chunks] or scored_chunks[:1]
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


def _build_paper_reading_context(query_terms: set[str], raw_paper_cache: list[dict[str, Any]]) -> list[dict[str, Any]]:
    scored_records: list[tuple[int, dict[str, Any]]] = []
    for raw_record in raw_paper_cache:
        if not isinstance(raw_record, dict):
            continue
        if not _paper_record_has_readable_excerpt(raw_record):
            continue
        score = _score_retrieval_paper(query_terms, raw_record)
        scored_records.append((score, raw_record))
    scored_records.sort(
        key=lambda item: (
            int(item[0]),
            1 if str(item[1].get("extract_confidence", "")).strip() == "high" else 0,
        ),
        reverse=True,
    )
    reading_context: list[dict[str, Any]] = []
    for score, record in scored_records[:MAX_RETRIEVAL_READING_PAPERS]:
        reading_chunks = _select_retrieval_chunks(query_terms, record, max_chunks=MAX_RETRIEVAL_READING_CHUNKS)
        reference = str(record.get("title", "")).strip() or str(record.get("source_id", "")).strip()
        abstract_excerpt = _truncate_retrieval_text(
            str(record.get("abstract", "")).strip(),
            limit=MAX_RETRIEVAL_CHUNK_CHARS,
        )
        excerpt_parts: list[str] = []
        if abstract_excerpt:
            excerpt_parts.append(f"Abstract: {abstract_excerpt}")
        for chunk in reading_chunks:
            section = str(chunk.get("section", "")).strip() or "Section"
            text = str(chunk.get("text", "")).strip()
            if not text:
                continue
            excerpt_parts.append(f"{section}: {text}")
        reading_context.append(
            {
                "reference": reference,
                "source_url": str(record.get("source_url", "")).strip(),
                "extract_confidence": str(record.get("extract_confidence", "")).strip(),
                "source_kind": str(record.get("source_kind", "")).strip(),
                "retrieval_priority": str(record.get("retrieval_priority", "")).strip(),
                "direct_reading_access": str(record.get("direct_reading_access", "")).strip(),
                "relevance_score": int(score),
                "paper_record_relpath": str(record.get("paper_record_relpath", "")).strip(),
                "paper_record_path": str(record.get("paper_record_path", "")).strip(),
                "download_relpath": str(record.get("download_relpath", "")).strip(),
                "download_path": str(record.get("download_path", "")).strip(),
                "abstract_excerpt": abstract_excerpt,
                "reading_chunks": [
                    {
                        "chunk_id": str(chunk.get("chunk_id", "")).strip(),
                        "section": str(chunk.get("section", "")).strip(),
                        "page": chunk.get("page"),
                        "text": str(chunk.get("text", "")).strip(),
                    }
                    for chunk in reading_chunks
                    if isinstance(chunk, dict) and str(chunk.get("text", "")).strip()
                ],
                "reading_excerpt": "\n\n".join(excerpt_parts).strip(),
            }
        )
    return reading_context


def _paper_record_has_readable_excerpt(record: dict[str, Any]) -> bool:
    abstract = str(record.get("abstract", "")).strip()
    if abstract:
        return True
    chunks_value = record.get("chunks", [])
    if not isinstance(chunks_value, list):
        return False
    return any(str(chunk.get("text", "")).strip() for chunk in chunks_value if isinstance(chunk, dict))


def _describe_retrieval_limitation(record: dict[str, Any]) -> str:
    direct_reading_access = str(record.get("direct_reading_access", "")).strip()
    extract_confidence = str(record.get("extract_confidence", "")).strip()
    source_kind = str(record.get("source_kind", "")).strip()
    if direct_reading_access == "image_only_pdf":
        return "cached PDF appears image-only, so no theorem-level excerpt was available"
    if direct_reading_access in {"metadata_only", "landing_page", "blocked"}:
        return "cached source resolves only to metadata or a landing page, so direct theorem-level reading was unavailable"
    if direct_reading_access == "discussion":
        return "cached source is only discussion/Q&A material, not a primary theorem-level text"
    if extract_confidence == "low":
        return "cached file was found but text extraction did not recover a usable theorem-level excerpt"
    if source_kind in {"portal_redirect", "metadata_portal", "qna"}:
        return "cached source is not a readable primary-paper extract"
    return "cached source did not expose a usable theorem-level excerpt"


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


def _build_paper_claim_retrieval_materials(candidate: dict[str, Any], materials: dict[str, Any]) -> dict[str, Any]:
    payload = dict(materials or {})
    if not payload:
        return {}

    query_terms = _build_retrieval_query_terms(candidate)
    query_term_set = set(query_terms)

    selected_papers: list[dict[str, Any]] = []
    readable_selected_papers: list[dict[str, Any]] = []
    literature_limitations: list[dict[str, str]] = []
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
        readable_selected_papers = [record for record in selected_papers if _paper_record_has_readable_excerpt(record)]
        for record in selected_papers:
            if record in readable_selected_papers:
                continue
            limitation = {
                "reference": str(record.get("title", "")).strip() or str(record.get("source_id", "")).strip(),
                "source_url": str(record.get("source_url", "")).strip(),
                "source_kind": str(record.get("source_kind", "")).strip(),
                "direct_reading_access": str(record.get("direct_reading_access", "")).strip(),
                "issue": _describe_retrieval_limitation(record),
            }
            if limitation not in literature_limitations:
                literature_limitations.append(limitation)

    selected_source_urls = {
        str(record.get("source_url", "")).strip()
        for record in readable_selected_papers or selected_papers
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
        "paper_claim": [str(item).strip() for item in payload.get("paper_claim", []) if str(item).strip()][:MAX_RETRIEVAL_PAPER_CLAIM_NOTES]
        if isinstance(payload.get("paper_claim", []), list)
        else [],
        "source_links": compact_source_links,
        "source_link_entries": compact_source_link_entries,
        "documents": _select_retrieval_documents(query_term_set, payload.get("documents", []))
        if isinstance(payload.get("documents", []), list)
        else [],
        "paper_cache": readable_selected_papers,
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
            for record in readable_selected_papers
        ],
        "paper_reading_context": _build_paper_reading_context(query_term_set, raw_paper_cache)
        if isinstance(raw_paper_cache, list)
        else [],
        "literature_limitations": literature_limitations,
        "retrieval_query_terms": query_terms,
    }
    if not compact_materials["paper_cache"] and selected_papers:
        compact_materials["paper_claim"] = list(compact_materials["paper_claim"]) + [
            "No cached theorem-level paper excerpt was readable for the top-ranked paper anchors; use source-link metadata only as a risk signal, not as direct-reading evidence."
        ]
    if compact_materials["paper_excerpt_context"] and literature_limitations:
        compact_materials["paper_claim"] = list(compact_materials["paper_claim"]) + [
            "Unreadable or extraction-thin anchors may still be dangerous baselines, but they should be treated as unresolved novelty risk rather than as direct-reading evidence."
        ]
    limited_source_links = compact_materials.get("source_link_entries", [])
    if isinstance(limited_source_links, list):
        for entry in limited_source_links:
            if not isinstance(entry, dict):
                continue
            reference = str(entry.get("label", "")).strip() or str(entry.get("url", "")).strip()
            direct_reading_access = str(entry.get("direct_reading_access", "")).strip()
            if (
                reference
                and direct_reading_access in WEAK_DIRECT_READING_ACCESS
                and not any(item.get("reference") == reference for item in literature_limitations)
            ):
                literature_limitations.append(
                    {
                        "reference": reference,
                        "source_url": str(entry.get("url", "")).strip(),
                        "source_kind": str(entry.get("source_kind", "")).strip(),
                        "direct_reading_access": direct_reading_access,
                        "issue": "source-link anchor is not directly readable enough for theorem-level comparison",
                    }
                )
    return compact_materials


def _validate_paper_claim_candidate(
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
        "missing_lemmas",
        "source_problem_ids",
        "theorem_pattern",
    }
    optional_keys = {
        "supporting_theorems",
        "context_note",
        "conceptual_depth_note",
    }
    raw_keys = set(raw_candidate.keys())
    if not required_keys.issubset(raw_keys) or not raw_keys.issubset(required_keys.union(optional_keys)):
        raise ValueError(f"paper_claim candidate {candidate_index} keys mismatch required contract")

    candidate_rank_seed = raw_candidate.get("candidate_rank_seed")
    if not isinstance(candidate_rank_seed, int):
        raise ValueError(f"paper_claim candidate {candidate_index} candidate_rank_seed must be an integer")

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
            f"paper_claim candidate {candidate_index} supporting_theorems, missing_lemmas, and source_problem_ids must be arrays"
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
            raise ValueError(f"paper_claim candidate {candidate_index} source_problem_id is not in tracked_problems: {problem_id}")
        seen_source_ids.add(problem_id)
        source_problem_ids.append(problem_id)

    if not statement:
        raise ValueError(f"paper_claim candidate {candidate_index} statement must be non-empty")
    if not docstring_summary:
        raise ValueError(f"paper_claim candidate {candidate_index} docstring_summary must be non-empty")
    if not rationale:
        raise ValueError(f"paper_claim candidate {candidate_index} rationale must be non-empty")
    if theorem_pattern not in PAPER_CLAIM_PATTERNS:
        raise ValueError(
            "paper_claim candidate theorem_pattern must be new_theorem|structure_discovery|framework_introduction"
        )
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


def validate_paper_claim_candidate_set_output(
    payload: dict[str, Any],
    expected_candidate_set_id: str,
    known_problem_ids: list[str],
) -> list[dict[str, Any]]:
    required_keys = {"candidate_set_id", "candidates"}
    if set(payload.keys()) != required_keys:
        raise ValueError("paper_claim_generate output keys mismatch required contract")

    candidate_set_id = str(payload.get("candidate_set_id", "")).strip()
    if candidate_set_id != expected_candidate_set_id:
        raise ValueError("paper_claim_generate candidate_set_id does not match request")

    raw_candidates = payload.get("candidates", [])
    if not isinstance(raw_candidates, list):
        raise ValueError("paper_claim_generate candidates must be an array")
    if len(raw_candidates) != PAPER_CLAIM_CANDIDATE_COUNT:
        raise ValueError(f"paper_claim_generate must return exactly {PAPER_CLAIM_CANDIDATE_COUNT} candidates")

    known_problem_id_set = {str(item).strip() for item in known_problem_ids if str(item).strip()}
    normalized_candidates: list[dict[str, Any]] = []
    seen_rank_seeds: set[int] = set()
    seen_statement_norms: set[str] = set()
    seen_theorem_name_stems: set[str] = set()
    theorem_patterns: set[str] = set()
    for candidate_index, item in enumerate(raw_candidates, start=1):
        if not isinstance(item, dict):
            raise ValueError("paper_claim_generate candidates must contain only objects")
        candidate = _validate_paper_claim_candidate(
            item,
            known_problem_id_set=known_problem_id_set,
            candidate_index=candidate_index,
        )
        candidate_rank_seed = int(candidate["candidate_rank_seed"])
        if candidate_rank_seed < 1 or candidate_rank_seed > PAPER_CLAIM_CANDIDATE_COUNT:
            raise ValueError("paper_claim_generate candidate_rank_seed must be within the fixed candidate set")
        if candidate_rank_seed in seen_rank_seeds:
            raise ValueError("paper_claim_generate candidate_rank_seed values must be unique")
        seen_rank_seeds.add(candidate_rank_seed)

        statement_norm = " ".join(str(candidate["statement"]).split()).lower()
        if statement_norm in seen_statement_norms:
            raise ValueError("paper_claim_generate candidate statements must be distinct")
        seen_statement_norms.add(statement_norm)

        theorem_name_stem = str(candidate["theorem_name_stem"])
        if theorem_name_stem in seen_theorem_name_stems:
            raise ValueError("paper_claim_generate theorem_name_stem values must be unique")
        seen_theorem_name_stems.add(theorem_name_stem)

        theorem_patterns.add(str(candidate["theorem_pattern"]))
        normalized_candidates.append(candidate)

    if seen_rank_seeds != set(range(1, PAPER_CLAIM_CANDIDATE_COUNT + 1)):
        raise ValueError("paper_claim_generate candidate_rank_seed values must cover the fixed candidate set")
    if len(theorem_patterns) < 2:
        raise ValueError("paper_claim_generate candidate set must contain at least two distinct theorem patterns")

    return sorted(normalized_candidates, key=lambda item: int(item["candidate_rank_seed"]))


def validate_paper_claim_selection_output(
    payload: dict[str, Any],
    *,
    expected_candidate_set_id: str,
    candidates: list[dict[str, Any]],
) -> tuple[int, str, list[dict[str, Any]]]:
    required_keys = {"candidate_set_id", "selected_candidate_rank_seed", "selection_summary", "ranking"}
    if set(payload.keys()) != required_keys:
        raise ValueError("paper_claim_select output keys mismatch required contract")

    candidate_set_id = str(payload.get("candidate_set_id", "")).strip()
    if candidate_set_id != expected_candidate_set_id:
        raise ValueError("paper_claim_select candidate_set_id does not match request")

    selected_candidate_rank_seed = payload.get("selected_candidate_rank_seed")
    if not isinstance(selected_candidate_rank_seed, int):
        raise ValueError("paper_claim_select selected_candidate_rank_seed must be an integer")

    selection_summary = str(payload.get("selection_summary", "")).strip()
    if not selection_summary:
        raise ValueError("paper_claim_select selection_summary must be non-empty")

    ranking_value = payload.get("ranking", [])
    if not isinstance(ranking_value, list):
        raise ValueError("paper_claim_select ranking must be an array")
    if len(ranking_value) != len(candidates):
        raise ValueError("paper_claim_select ranking length must match candidate count")

    candidate_rank_seed_set = {int(candidate["candidate_rank_seed"]) for candidate in candidates}
    normalized_ranking: list[dict[str, Any]] = []
    seen_candidate_rank_seeds: set[int] = set()
    seen_ranks: set[int] = set()
    selected_entries = 0
    for item in ranking_value:
        if not isinstance(item, dict):
            raise ValueError("paper_claim_select ranking entries must be objects")
        if set(item.keys()) != {"candidate_rank_seed", "rank", "decision", "reason"}:
            raise ValueError("paper_claim_select ranking entry keys mismatch required contract")

        candidate_rank_seed = item.get("candidate_rank_seed")
        rank = item.get("rank")
        if not isinstance(candidate_rank_seed, int) or not isinstance(rank, int):
            raise ValueError("paper_claim_select ranking candidate_rank_seed and rank must be integers")
        decision = str(item.get("decision", "")).strip()
        reason = str(item.get("reason", "")).strip()
        if candidate_rank_seed not in candidate_rank_seed_set:
            raise ValueError("paper_claim_select ranking candidate_rank_seed must refer to an input candidate")
        if candidate_rank_seed in seen_candidate_rank_seeds:
            raise ValueError("paper_claim_select ranking candidate_rank_seed values must be unique")
        if rank < 1 or rank > len(candidates):
            raise ValueError("paper_claim_select ranking rank is out of bounds")
        if rank in seen_ranks:
            raise ValueError("paper_claim_select ranking rank values must be unique")
        if decision not in {"select", "reject"}:
            raise ValueError("paper_claim_select decision must be select or reject")
        if not reason:
            raise ValueError("paper_claim_select reason must be non-empty")
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
        raise ValueError("paper_claim_select ranking must cover each input candidate exactly once")
    if seen_ranks != set(range(1, len(candidates) + 1)):
        raise ValueError("paper_claim_select ranking must cover every rank exactly once")
    if selected_entries != 1:
        raise ValueError("paper_claim_select must mark exactly one candidate as select")
    if selected_candidate_rank_seed not in candidate_rank_seed_set:
        raise ValueError("paper_claim_select selected_candidate_rank_seed must refer to an input candidate")

    ranking_by_rank = {int(item["rank"]): item for item in normalized_ranking}
    top_entry = ranking_by_rank[1]
    if int(top_entry["candidate_rank_seed"]) != selected_candidate_rank_seed or str(top_entry["decision"]) != "select":
        raise ValueError("paper_claim_select rank 1 must be the selected candidate")
    for rank in range(2, len(candidates) + 1):
        if str(ranking_by_rank[rank]["decision"]) != "reject":
            raise ValueError("paper_claim_select ranks below 1 must be rejected")

    return selected_candidate_rank_seed, selection_summary, sorted(normalized_ranking, key=lambda item: int(item["rank"]))


def validate_paper_claim_suggestion_output(
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
        "missing_lemmas",
        "source_problem_ids",
        "theorem_pattern",
    }
    optional_keys = {
        "supporting_theorems",
        "context_note",
        "conceptual_depth_note",
    }
    payload_keys = set(payload.keys())
    if not required_keys.issubset(payload_keys) or not payload_keys.issubset(required_keys.union(optional_keys)):
        raise ValueError("paper_claim_suggest output keys mismatch required contract")

    candidate_id = str(payload.get("candidate_id", "")).strip()
    if candidate_id != expected_candidate_id:
        raise ValueError("paper_claim_suggest candidate_id does not match request")
    if str(payload.get("result", "")).strip() != "ok":
        raise ValueError("paper_claim_suggest result must be ok")

    candidate = _validate_paper_claim_candidate(
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


def validate_paper_claim_retrieval_output(
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
        raise ValueError("paper_claim_retrieve output keys mismatch required contract")

    candidate_id = str(payload.get("candidate_id", "")).strip()
    if candidate_id != expected_candidate_id:
        raise ValueError("paper_claim_retrieve candidate_id does not match request")

    closest_items_value = payload.get("closest_items", [])
    if not isinstance(closest_items_value, list):
        raise ValueError("paper_claim_retrieve closest_items must be an array")
    normalized_items: list[dict[str, Any]] = []
    for item_index, item in enumerate(closest_items_value, start=1):
        if not isinstance(item, dict):
            raise ValueError("paper_claim_retrieve closest_items must contain only objects")
        if set(item.keys()) != {"reference", "kind", "relevance", "confidence"}:
            raise ValueError(f"paper_claim_retrieve closest_item {item_index} keys mismatch required contract")
        reference = str(item.get("reference", "")).strip()
        kind = str(item.get("kind", "")).strip()
        relevance = str(item.get("relevance", "")).strip()
        confidence = str(item.get("confidence", "")).strip()
        if not reference or not kind or not relevance:
            raise ValueError(f"paper_claim_retrieve closest_item {item_index} fields must be non-empty")
        if confidence not in {"high", "medium", "low"}:
            raise ValueError("paper_claim_retrieve closest_item confidence must be high|medium|low")
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
        raise ValueError("paper_claim_retrieve missing_angles must be an array")
    missing_angles = [str(item).strip() for item in missing_angles_value if str(item).strip()]

    research_line = str(payload.get("research_line", "")).strip()
    coverage_assessment = str(payload.get("coverage_assessment", "")).strip()
    need_supplemental_retrieval = payload.get("need_supplemental_retrieval")
    if not research_line or not coverage_assessment:
        raise ValueError("paper_claim_retrieve research_line and coverage_assessment must be non-empty")
    if not isinstance(need_supplemental_retrieval, bool):
        raise ValueError("paper_claim_retrieve need_supplemental_retrieval must be a boolean")

    return {
        "candidate_id": candidate_id,
        "closest_items": normalized_items,
        "research_line": research_line,
        "coverage_assessment": coverage_assessment,
        "missing_angles": missing_angles,
        "need_supplemental_retrieval": need_supplemental_retrieval,
    }


def validate_paper_claim_mapping_output(
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
        raise ValueError("paper_claim_map output keys mismatch required contract")

    candidate_id = str(payload.get("candidate_id", "")).strip()
    if candidate_id != expected_candidate_id:
        raise ValueError("paper_claim_map candidate_id does not match request")

    relations_value = payload.get("relations", [])
    if not isinstance(relations_value, list):
        raise ValueError("paper_claim_map relations must be an array")
    relations: list[dict[str, Any]] = []
    for relation_index, item in enumerate(relations_value, start=1):
        if not isinstance(item, dict):
            raise ValueError("paper_claim_map relations must contain only objects")
        if set(item.keys()) != {"reference", "overlap", "delta", "delta_materiality"}:
            raise ValueError(f"paper_claim_map relation {relation_index} keys mismatch required contract")
        reference = str(item.get("reference", "")).strip()
        overlap = str(item.get("overlap", "")).strip()
        delta = str(item.get("delta", "")).strip()
        delta_materiality = str(item.get("delta_materiality", "")).strip()
        if not reference or not overlap or not delta:
            raise ValueError(f"paper_claim_map relation {relation_index} fields must be non-empty")
        if delta_materiality not in {"substantial", "unclear", "minor"}:
            raise ValueError("paper_claim_map delta_materiality must be substantial|unclear|minor")
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
        raise ValueError("paper_claim_map closest_baseline and variant_objection must be non-empty")
    if overall_novelty_risk not in {"high", "medium", "low"}:
        raise ValueError("paper_claim_map overall_novelty_risk must be high|medium|low")

    return {
        "candidate_id": candidate_id,
        "closest_baseline": closest_baseline,
        "relations": relations,
        "overall_novelty_risk": overall_novelty_risk,
        "variant_objection": variant_objection,
    }


def validate_paper_claim_evaluation_output(
    payload: dict[str, Any],
    *,
    expected_candidate_id: str,
) -> dict[str, Any]:
    required_keys = {
        "candidate_id",
        "baseline_delta_supported",
        "novelty",
        "significance",
        "paper_unit_viability",
        "conciseness",
        "strongest_positive_signal",
        "strongest_objection",
        "objection_answerable",
        "minimal_publishable_unit",
        "salvage_plan",
        "rejection_tags",
        "verdict",
        "reason",
    }
    if set(payload.keys()) != required_keys:
        raise ValueError("paper_claim_evaluate output keys mismatch required contract")

    candidate_id = str(payload.get("candidate_id", "")).strip()
    if candidate_id != expected_candidate_id:
        raise ValueError("paper_claim_evaluate candidate_id does not match request")

    baseline_delta_supported = str(payload.get("baseline_delta_supported", "")).strip()
    novelty = str(payload.get("novelty", "")).strip()
    significance = str(payload.get("significance", "")).strip()
    paper_unit_viability = str(payload.get("paper_unit_viability", "")).strip()
    conciseness = str(payload.get("conciseness", "")).strip()
    strongest_positive_signal = str(payload.get("strongest_positive_signal", "")).strip()
    strongest_objection = str(payload.get("strongest_objection", "")).strip()
    objection_answerable = str(payload.get("objection_answerable", "")).strip()
    minimal_publishable_unit = str(payload.get("minimal_publishable_unit", "")).strip()
    salvage_plan = str(payload.get("salvage_plan", "")).strip()
    raw_rejection_tags = payload.get("rejection_tags", [])
    verdict = str(payload.get("verdict", "")).strip()
    reason = str(payload.get("reason", "")).strip()

    if baseline_delta_supported not in {"yes", "partial", "no"}:
        raise ValueError("paper_claim_evaluate baseline_delta_supported must be yes|partial|no")
    if novelty not in {"high", "medium", "low"}:
        raise ValueError("paper_claim_evaluate novelty must be high|medium|low")
    if significance not in {"high", "medium", "low"}:
        raise ValueError("paper_claim_evaluate significance must be high|medium|low")
    if paper_unit_viability not in {"yes", "borderline", "no"}:
        raise ValueError("paper_claim_evaluate paper_unit_viability must be yes|borderline|no")
    if conciseness not in {"yes", "borderline", "no"}:
        raise ValueError("paper_claim_evaluate conciseness must be yes|borderline|no")
    if objection_answerable not in {"yes", "partial", "no"}:
        raise ValueError("paper_claim_evaluate objection_answerable must be yes|partial|no")
    if verdict not in {"pass", "revise", "reject"}:
        raise ValueError("paper_claim_evaluate verdict must be pass|revise|reject")
    if not isinstance(raw_rejection_tags, list):
        raise ValueError("paper_claim_evaluate rejection_tags must be a list")
    rejection_tags: list[str] = []
    for raw_tag in raw_rejection_tags:
        tag = str(raw_tag).strip()
        if not tag:
            raise ValueError("paper_claim_evaluate rejection_tags must not contain empty entries")
        if tag not in PAPER_CLAIM_REJECTION_TAGS:
            raise ValueError(f"paper_claim_evaluate rejection_tags contains unknown tag: {tag}")
        if tag not in rejection_tags:
            rejection_tags.append(tag)
    if verdict == "pass" and rejection_tags:
        raise ValueError("paper_claim_evaluate rejection_tags must be empty when verdict is pass")
    if verdict in {"revise", "reject"} and not rejection_tags:
        raise ValueError("paper_claim_evaluate rejection_tags must be non-empty when verdict is revise|reject")
    hard_pass_gate = (
        baseline_delta_supported == "yes"
        and conciseness == "yes"
        and paper_unit_viability == "yes"
        and objection_answerable == "yes"
        and novelty != "low"
        and significance != "low"
    )
    heavy_revise_gate = (
        paper_unit_viability == "borderline"
        and objection_answerable != "no"
        and baseline_delta_supported in {"yes", "partial"}
        and conciseness in {"yes", "borderline"}
        and _looks_like_single_repair_step(salvage_plan)
    )
    if verdict == "pass" and not hard_pass_gate:
        raise ValueError("paper_claim_evaluate pass requires the hard pass gate to be fully satisfied")
    if verdict != "pass" and hard_pass_gate:
        raise ValueError("paper_claim_evaluate must return pass when the hard pass gate is fully satisfied")
    if verdict == "revise" and not heavy_revise_gate:
        raise ValueError(
            "paper_claim_evaluate revise requires the heavy revise gate to be satisfied: "
            + _json_compact_debug(
                {
                    "paper_unit_viability": paper_unit_viability,
                    "objection_answerable": objection_answerable,
                    "baseline_delta_supported": baseline_delta_supported,
                    "conciseness": conciseness,
                    "single_repair_step": _looks_like_single_repair_step(salvage_plan),
                }
            )
        )
    if verdict == "reject" and heavy_revise_gate and not hard_pass_gate:
        raise ValueError("paper_claim_evaluate should use revise when the heavy revise gate is satisfied")
    if not strongest_positive_signal or not strongest_objection or not minimal_publishable_unit or not reason:
        raise ValueError(
            "paper_claim_evaluate strongest_positive_signal, strongest_objection, minimal_publishable_unit, and reason must be non-empty"
        )

    return {
        "candidate_id": candidate_id,
        "baseline_delta_supported": baseline_delta_supported,
        "novelty": novelty,
        "significance": significance,
        "paper_unit_viability": paper_unit_viability,
        "conciseness": conciseness,
        "strongest_positive_signal": strongest_positive_signal,
        "strongest_objection": strongest_objection,
        "objection_answerable": objection_answerable,
        "minimal_publishable_unit": minimal_publishable_unit,
        "salvage_plan": salvage_plan,
        "rejection_tags": rejection_tags,
        "verdict": verdict,
        "reason": reason,
    }


def validate_problem_design_cluster_output(payload: dict[str, Any]) -> list[dict[str, Any]]:
    if set(payload.keys()) != {"clusters"}:
        raise ValueError("problem_design_cluster output keys mismatch required contract")

    raw_clusters = payload.get("clusters", [])
    if not isinstance(raw_clusters, list):
        raise ValueError("problem_design_cluster clusters must be an array")
    if not raw_clusters or len(raw_clusters) > MAX_PROBLEM_DESIGN_CLUSTERS:
        raise ValueError(
            f"problem_design_cluster must return between 1 and {MAX_PROBLEM_DESIGN_CLUSTERS} clusters"
        )

    normalized_clusters: list[dict[str, Any]] = []
    seen_cluster_ids: set[str] = set()
    for cluster_index, raw_cluster in enumerate(raw_clusters, start=1):
        if not isinstance(raw_cluster, dict):
            raise ValueError("problem_design_cluster clusters must contain only objects")
        cluster = _normalize_problem_design_cluster(raw_cluster, cluster_index=cluster_index)
        cluster_id = str(cluster["cluster_id"])
        if cluster_id in seen_cluster_ids:
            raise ValueError("problem_design_cluster cluster_id values must be unique")
        seen_cluster_ids.add(cluster_id)
        normalized_clusters.append(cluster)
    return normalized_clusters


def validate_problem_design_context_output(
    payload: dict[str, Any],
    *,
    expected_cluster_id: str,
) -> dict[str, Any]:
    return _normalize_problem_design_contextualization(payload, expected_cluster_id=expected_cluster_id)


def validate_problem_design_core_extract_output(
    payload: dict[str, Any],
    *,
    expected_problem_id: str,
    known_cluster_ids: list[str],
) -> dict[str, Any]:
    required_keys = {
        "problem_id",
        "cluster_id",
        "headline_claim",
        "core_mathematical_content",
        "literature_context",
        "supporting_claims",
        "no_go_faces",
        "proof_assets",
        "why_this_face",
    }
    if set(payload.keys()) != required_keys:
        raise ValueError("problem_design_core_extract output keys mismatch required contract")

    problem_id = str(payload.get("problem_id", "")).strip()
    cluster_id = str(payload.get("cluster_id", "")).strip()
    headline_claim = str(payload.get("headline_claim", "")).strip()
    core_mathematical_content = str(payload.get("core_mathematical_content", "")).strip()
    literature_context_value = payload.get("literature_context", {})
    supporting_claims_value = payload.get("supporting_claims", [])
    no_go_faces_value = payload.get("no_go_faces", [])
    proof_assets_value = payload.get("proof_assets", [])
    why_this_face = str(payload.get("why_this_face", "")).strip()
    if problem_id != expected_problem_id:
        raise ValueError("problem_design_core_extract problem_id does not match request")
    if not cluster_id or not headline_claim or not core_mathematical_content or not why_this_face:
        raise ValueError("problem_design_core_extract fields must be non-empty")
    if (
        not isinstance(literature_context_value, dict)
        or not isinstance(supporting_claims_value, list)
        or not isinstance(no_go_faces_value, list)
        or not isinstance(proof_assets_value, list)
    ):
        raise ValueError(
            "problem_design_core_extract literature_context must be an object and supporting_claims, no_go_faces, proof_assets must be arrays"
        )
    if known_cluster_ids and cluster_id not in {str(item).strip() for item in known_cluster_ids if str(item).strip()}:
        raise ValueError("problem_design_core_extract cluster_id is invalid")
    if set(literature_context_value.keys()) != {
        "closest_baseline",
        "routine_reading_risk",
        "possible_opening",
    }:
        raise ValueError("problem_design_core_extract literature_context keys mismatch required contract")
    literature_context = {
        "closest_baseline": str(literature_context_value.get("closest_baseline", "")).strip(),
        "routine_reading_risk": str(literature_context_value.get("routine_reading_risk", "")).strip(),
        "possible_opening": str(literature_context_value.get("possible_opening", "")).strip(),
    }
    if not all(literature_context.values()):
        raise ValueError("problem_design_core_extract literature_context fields must be non-empty")
    return {
        "problem_id": problem_id,
        "cluster_id": cluster_id,
        "headline_claim": headline_claim,
        "core_mathematical_content": core_mathematical_content,
        "literature_context": literature_context,
        "supporting_claims": [str(item).strip() for item in supporting_claims_value if str(item).strip()],
        "no_go_faces": [str(item).strip() for item in no_go_faces_value if str(item).strip()],
        "proof_assets": [str(item).strip() for item in proof_assets_value if str(item).strip()],
        "why_this_face": why_this_face,
    }


def request_problem_design_clusters(
    *,
    worker_settings: Any,
    prompt: str,
    derived_entries: list[dict[str, str]],
    current_iteration: int,
    guidance: dict[str, Any],
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    theory_state, _, _ = unpack_guidance_context(guidance)
    payload = {
        "current_iteration": current_iteration,
        "derived_theorems": [
            {
                "name": str(entry.get("name", "")),
                "statement": str(entry.get("statement", "")),
            }
            for entry in derived_entries
        ],
        "theory_state": _build_paper_claim_conceptual_theory_state(theory_state),
    }
    response, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="problem_design_cluster",
        system_prompt=prompt,
        payload=payload,
        metadata={"derived_theorem_count": len(derived_entries)},
    )
    return validate_problem_design_cluster_output(response), worker_meta


def request_problem_design_contextualization(
    *,
    worker_settings: Any,
    prompt: str,
    cluster: dict[str, Any],
    current_iteration: int,
    guidance: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    _, _, materials = unpack_guidance_context(guidance)
    contextualization_materials = _build_problem_design_cluster_materials(cluster, materials)
    payload = {
        "cluster_id": str(cluster["cluster_id"]),
        "current_iteration": current_iteration,
        "cluster": cluster,
        "materials": contextualization_materials,
    }
    response, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="problem_design_contextualize",
        system_prompt=prompt,
        payload=payload,
        metadata={
            "cluster_id": str(cluster["cluster_id"]),
            "paper_excerpt_count": len(contextualization_materials.get("paper_excerpt_context", [])),
        },
    )
    return (
        validate_problem_design_context_output(
            response,
            expected_cluster_id=str(cluster["cluster_id"]),
        ),
        worker_meta,
    )


def request_problem_design_core_extract(
    *,
    worker_settings: Any,
    prompt: str,
    problem_id: str,
    current_iteration: int,
    guidance: dict[str, Any],
    cluster_context: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    theory_state, _, materials = unpack_guidance_context(guidance)
    payload = {
        "problem_id": problem_id,
        "current_iteration": current_iteration,
        "cluster_context": cluster_context,
        "theory_state": _build_paper_claim_conceptual_theory_state(theory_state),
        "materials": _build_problem_design_seed_materials(
            _build_paper_claim_conceptual_theory_state(theory_state),
            materials,
        ),
    }
    response, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="problem_design_core_extract",
        system_prompt=prompt,
        payload=payload,
        metadata={"problem_id": problem_id, "cluster_id": str(cluster_context.get("cluster_id", "")).strip()},
    )
    return (
        validate_problem_design_core_extract_output(
            response,
            expected_problem_id=problem_id,
            known_cluster_ids=[str(cluster_context.get("cluster_id", "")).strip()],
        ),
        worker_meta,
    )


def run_problem_design_contextualization(
    *,
    worker_settings: Any,
    guidance: dict[str, Any],
    derived_entries: list[dict[str, str]],
    current_iteration: int,
    phase_logs: bool,
    run_id: str,
    phase_attempts_path: Path | None,
    session_events_path: Path | None,
    cluster_prompt: str,
    contextualize_prompt: str,
) -> tuple[list[dict[str, Any]] | None, str, str]:
    phase = "problem_design_cluster"
    _append_paper_claim_session_event(
        session_events_path,
        event=f"{phase}_started",
        run_id=run_id,
        iteration=current_iteration,
        candidate_set_id="problem_design_clusters",
        payload={"derived_theorem_count": len(derived_entries)},
    )
    emit_phase_log(
        phase_logs,
        phase,
        iteration=current_iteration,
        derived_theorem_count=len(derived_entries),
    )
    started_monotonic = time.monotonic()
    started_at = iso_timestamp_now()
    try:
        clusters, _ = request_problem_design_clusters(
            worker_settings=worker_settings,
            prompt=cluster_prompt,
            derived_entries=derived_entries,
            current_iteration=current_iteration,
            guidance=guidance,
        )
    except (RuntimeError, ValueError) as exc:
        failed_error = str(exc)
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type="paper_claim_session",
            iteration=current_iteration,
            entity_id="problem_design_clusters",
            phase=phase,
            worker_task=phase,
            started_at=started_at,
            finished_at=iso_timestamp_now(),
            duration_ms=monotonic_duration_ms(started_monotonic),
            success=False,
            result="error",
            error=failed_error,
        )
        _append_paper_claim_session_event(
            session_events_path,
            event=f"{phase}_result",
            run_id=run_id,
            iteration=current_iteration,
            candidate_set_id="problem_design_clusters",
            payload={"status": "error", "error": failed_error},
        )
        return None, phase, failed_error
    append_phase_attempt_record(
        phase_attempts_path,
        run_id=run_id,
        session_type="paper_claim_session",
        iteration=current_iteration,
        entity_id="problem_design_clusters",
        phase=phase,
        worker_task=phase,
        started_at=started_at,
        finished_at=iso_timestamp_now(),
        duration_ms=monotonic_duration_ms(started_monotonic),
        success=True,
        result="ok",
    )
    _append_paper_claim_session_event(
        session_events_path,
        event=f"{phase}_result",
        run_id=run_id,
        iteration=current_iteration,
        candidate_set_id="problem_design_clusters",
        payload={"status": "ok", "clusters": clusters},
    )

    cluster_contexts: list[dict[str, Any]] = []
    for cluster in clusters:
        cluster_id = str(cluster["cluster_id"])
        phase = "problem_design_contextualize"
        _append_paper_claim_session_event(
            session_events_path,
            event=f"{phase}_started",
            run_id=run_id,
            iteration=current_iteration,
            candidate_set_id=cluster_id,
            payload={
                "cluster_id": cluster_id,
                "cluster_theme": str(cluster["cluster_theme"]),
                "member_theorem_count": len(cluster.get("member_theorems", [])),
            },
        )
        emit_phase_log(
            phase_logs,
            phase,
            iteration=current_iteration,
            cluster_id=cluster_id,
            cluster_theme=str(cluster["cluster_theme"]),
        )
        started_monotonic = time.monotonic()
        started_at = iso_timestamp_now()
        try:
            contextualization, _ = request_problem_design_contextualization(
                worker_settings=worker_settings,
                prompt=contextualize_prompt,
                cluster=cluster,
                current_iteration=current_iteration,
                guidance=guidance,
            )
        except (RuntimeError, ValueError) as exc:
            failed_error = str(exc)
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type="paper_claim_session",
                iteration=current_iteration,
                entity_id=cluster_id,
                phase=phase,
                worker_task=phase,
                started_at=started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(started_monotonic),
                success=False,
                result="error",
                error=failed_error,
            )
            _append_paper_claim_session_event(
                session_events_path,
                event=f"{phase}_result",
                run_id=run_id,
                iteration=current_iteration,
                candidate_set_id=cluster_id,
                payload={"status": "error", "error": failed_error},
            )
            return None, phase, failed_error
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type="paper_claim_session",
            iteration=current_iteration,
            entity_id=cluster_id,
            phase=phase,
            worker_task=phase,
            started_at=started_at,
            finished_at=iso_timestamp_now(),
            duration_ms=monotonic_duration_ms(started_monotonic),
            success=True,
            result="ok",
        )
        cluster_context = {**cluster, **contextualization}
        cluster_contexts.append(cluster_context)
        _append_paper_claim_session_event(
            session_events_path,
            event=f"{phase}_result",
            run_id=run_id,
            iteration=current_iteration,
            candidate_set_id=cluster_id,
            payload={
                "status": "ok",
                "cluster_id": cluster_id,
                "cluster_theme": str(cluster_context["cluster_theme"]),
                "headline_viability": str(cluster_context["paper_core_analysis"]["headline_viability"]),
                "external_baseline_pressure": str(
                    cluster_context["external_positioning"]["external_baseline_pressure"]
                ),
                "closest_baseline": str(
                    cluster_context["external_positioning"]["closest_baselines"][0]["reference"]
                )
                if cluster_context["external_positioning"]["closest_baselines"]
                else "",
            },
        )

    _append_paper_claim_session_event(
        session_events_path,
        event="problem_design_contextualization_summary",
        run_id=run_id,
        iteration=current_iteration,
        candidate_set_id="problem_design_clusters",
        payload={
            "cluster_count": len(clusters),
            "contextualized_cluster_count": len(cluster_contexts),
            "cluster_ids": [str(item["cluster_id"]) for item in cluster_contexts],
        },
    )
    return cluster_contexts, "", ""


def build_problem_design_dossiers(
    *,
    worker_settings: Any,
    guidance: dict[str, Any],
    cluster_contexts: list[dict[str, Any]],
    current_iteration: int,
    phase_logs: bool,
    run_id: str,
    phase_attempts_path: Path | None,
    session_events_path: Path | None,
    core_extract_prompt: str,
) -> tuple[list[dict[str, Any]] | None, str, str]:
    dossiers: list[dict[str, Any]] = []
    failed_stage = ""
    failed_error = ""

    for cluster_index, cluster_context in enumerate(cluster_contexts, start=1):
        problem_id = f"pd_paper_claim_{cluster_index:02d}"
        cluster_id = str(cluster_context.get("cluster_id", "")).strip()
        _append_paper_claim_session_event(
            session_events_path,
            event="problem_design_dossier_started",
            run_id=run_id,
            iteration=current_iteration,
            candidate_set_id=problem_id,
            payload={
                "problem_id": problem_id,
                "cluster_id": cluster_id,
                "cluster_index": cluster_index,
            },
        )

        phase = "problem_design_core_extract"
        _append_paper_claim_session_event(
            session_events_path,
            event=f"{phase}_started",
            run_id=run_id,
            iteration=current_iteration,
            candidate_set_id=problem_id,
            payload={
                "problem_id": problem_id,
                "cluster_id": cluster_id,
            },
        )
        emit_phase_log(
            phase_logs,
            phase,
            iteration=current_iteration,
            problem_id=problem_id,
            cluster_id=cluster_id,
        )
        started_monotonic = time.monotonic()
        started_at = iso_timestamp_now()
        try:
            core_dossier, _ = request_problem_design_core_extract(
                worker_settings=worker_settings,
                prompt=core_extract_prompt,
                problem_id=problem_id,
                current_iteration=current_iteration,
                guidance=guidance,
                cluster_context=cluster_context,
            )
        except (RuntimeError, ValueError) as exc:
            failed_stage = phase
            failed_error = str(exc)
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type="paper_claim_session",
                iteration=current_iteration,
                entity_id=problem_id,
                phase=phase,
                worker_task=phase,
                started_at=started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(started_monotonic),
                success=False,
                result="error",
                error=failed_error,
            )
            _append_paper_claim_session_event(
                session_events_path,
                event=f"{phase}_result",
                run_id=run_id,
                iteration=current_iteration,
                candidate_set_id=problem_id,
                payload={"status": "error", "error": failed_error},
            )
            return None, failed_stage, failed_error
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type="paper_claim_session",
            iteration=current_iteration,
            entity_id=problem_id,
            phase=phase,
            worker_task=phase,
            started_at=started_at,
            finished_at=iso_timestamp_now(),
            duration_ms=monotonic_duration_ms(started_monotonic),
            success=True,
            result="ok",
        )
        _append_paper_claim_session_event(
            session_events_path,
            event=f"{phase}_result",
            run_id=run_id,
            iteration=current_iteration,
            candidate_set_id=problem_id,
            payload={"status": "ok", "core_dossier": core_dossier},
        )
        dossier = {
            "problem_id": problem_id,
            "cluster_id": str(core_dossier["cluster_id"]),
            "cluster_theme": str(cluster_context.get("cluster_theme", "")).strip(),
            "cluster_summary": str(cluster_context.get("cluster_summary", "")).strip(),
            "headline_claim": str(core_dossier["headline_claim"]),
            "core_mathematical_content": str(core_dossier["core_mathematical_content"]),
            "literature_context": dict(core_dossier["literature_context"]),
            "supporting_claims": list(core_dossier["supporting_claims"]),
            "no_go_faces": list(core_dossier["no_go_faces"]),
            "proof_assets": list(core_dossier["proof_assets"]),
            "why_this_face": str(core_dossier["why_this_face"]),
        }
        dossiers.append(dossier)
        _append_paper_claim_session_event(
            session_events_path,
            event="problem_design_dossier_summary",
            run_id=run_id,
            iteration=current_iteration,
            candidate_set_id=problem_id,
            payload={
                "problem_id": problem_id,
                "cluster_id": cluster_id,
                "headline_claim": str(core_dossier["headline_claim"]),
                "closest_baseline": str(core_dossier["literature_context"]["closest_baseline"]),
                "proof_asset_count": len(core_dossier["proof_assets"]),
            },
        )

    if not dossiers:
        return None, "problem_design_dossier_build", "no problem design dossiers were produced"
    return dossiers, failed_stage, failed_error


def _build_paper_claim_dossier_retrieval_materials(dossier: dict[str, Any], materials: dict[str, Any]) -> dict[str, Any]:
    proxy_candidate = {
        "statement": str(dossier.get("headline_claim", "")).strip(),
        "rationale": "\n".join(
            part
            for part in (
                str(dossier.get("core_mathematical_content", "")).strip(),
                str(dossier.get("why_this_face", "")).strip(),
            )
            if part
        ),
        "theorem_name_stem": str(dossier.get("problem_id", "")).strip() or "paper_claim",
    }
    return _build_paper_claim_retrieval_materials(proxy_candidate, materials)


def validate_paper_claim_retrieval_output(
    payload: dict[str, Any],
    *,
    expected_problem_id: str,
) -> dict[str, Any]:
    required_keys = {
        "problem_id",
        "closest_items",
        "directly_read_evidence",
        "coverage_assessment",
        "missing_angles",
        "need_supplemental_retrieval",
    }
    if set(payload.keys()) != required_keys:
        raise ValueError("paper_claim_retrieve output keys mismatch required contract")

    problem_id = str(payload.get("problem_id", "")).strip()
    if problem_id != expected_problem_id:
        raise ValueError("paper_claim_retrieve problem_id does not match request")

    raw_closest_items = payload.get("closest_items", [])
    raw_direct_evidence = payload.get("directly_read_evidence", [])
    raw_missing_angles = payload.get("missing_angles", [])
    if not isinstance(raw_closest_items, list):
        raise ValueError("paper_claim_retrieve closest_items must be an array")
    if not isinstance(raw_direct_evidence, list):
        raise ValueError("paper_claim_retrieve directly_read_evidence must be an array")
    if not isinstance(raw_missing_angles, list):
        raise ValueError("paper_claim_retrieve missing_angles must be an array")

    closest_items: list[dict[str, Any]] = []
    for item_index, item in enumerate(raw_closest_items, start=1):
        if not isinstance(item, dict):
            raise ValueError("paper_claim_retrieve closest_items must contain only objects")
        if set(item.keys()) != {"reference", "kind", "relevance", "confidence"}:
            raise ValueError(f"paper_claim_retrieve closest_item {item_index} keys mismatch required contract")
        reference = str(item.get("reference", "")).strip()
        kind = str(item.get("kind", "")).strip()
        relevance = str(item.get("relevance", "")).strip()
        confidence = str(item.get("confidence", "")).strip()
        if not reference or not kind or not relevance:
            raise ValueError(f"paper_claim_retrieve closest_item {item_index} fields must be non-empty")
        if confidence not in {"high", "medium", "low"}:
            raise ValueError("paper_claim_retrieve closest_item confidence must be high|medium|low")
        closest_items.append(
            {
                "reference": reference,
                "kind": kind,
                "relevance": relevance,
                "confidence": confidence,
            }
        )

    directly_read_evidence: list[dict[str, Any]] = []
    for evidence_index, item in enumerate(raw_direct_evidence, start=1):
        if not isinstance(item, dict):
            raise ValueError("paper_claim_retrieve directly_read_evidence must contain only objects")
        if set(item.keys()) != {"reference", "evidence", "supports", "confidence"}:
            raise ValueError(
                f"paper_claim_retrieve directly_read_evidence {evidence_index} keys mismatch required contract"
            )
        reference = str(item.get("reference", "")).strip()
        evidence = str(item.get("evidence", "")).strip()
        supports = str(item.get("supports", "")).strip()
        confidence = str(item.get("confidence", "")).strip()
        if not reference or not evidence or not supports:
            raise ValueError(
                f"paper_claim_retrieve directly_read_evidence {evidence_index} fields must be non-empty"
            )
        if confidence not in {"high", "medium", "low"}:
            raise ValueError("paper_claim_retrieve directly_read_evidence confidence must be high|medium|low")
        directly_read_evidence.append(
            {
                "reference": reference,
                "evidence": evidence,
                "supports": supports,
                "confidence": confidence,
            }
        )

    coverage_assessment = str(payload.get("coverage_assessment", "")).strip()
    need_supplemental_retrieval = payload.get("need_supplemental_retrieval")
    if not coverage_assessment:
        raise ValueError("paper_claim_retrieve coverage_assessment must be non-empty")
    if not isinstance(need_supplemental_retrieval, bool):
        raise ValueError("paper_claim_retrieve need_supplemental_retrieval must be a boolean")

    return {
        "problem_id": problem_id,
        "closest_items": closest_items,
        "directly_read_evidence": directly_read_evidence,
        "coverage_assessment": coverage_assessment,
        "missing_angles": [str(item).strip() for item in raw_missing_angles if str(item).strip()],
        "need_supplemental_retrieval": need_supplemental_retrieval,
    }


def validate_paper_claim_mapping_output(
    payload: dict[str, Any],
    *,
    expected_problem_id: str,
) -> dict[str, Any]:
    required_keys = {
        "problem_id",
        "closest_baseline",
        "relations",
        "theorem_face_assessment",
        "baseline_delta",
        "outsider_risk",
    }
    if set(payload.keys()) != required_keys:
        raise ValueError("paper_claim_map output keys mismatch required contract")

    problem_id = str(payload.get("problem_id", "")).strip()
    if problem_id != expected_problem_id:
        raise ValueError("paper_claim_map problem_id does not match request")

    raw_relations = payload.get("relations", [])
    if not isinstance(raw_relations, list):
        raise ValueError("paper_claim_map relations must be an array")
    relations: list[dict[str, Any]] = []
    for relation_index, item in enumerate(raw_relations, start=1):
        if not isinstance(item, dict):
            raise ValueError("paper_claim_map relations must contain only objects")
        if set(item.keys()) != {"reference", "overlap", "delta", "delta_materiality"}:
            raise ValueError(f"paper_claim_map relation {relation_index} keys mismatch required contract")
        reference = str(item.get("reference", "")).strip()
        overlap = str(item.get("overlap", "")).strip()
        delta = str(item.get("delta", "")).strip()
        delta_materiality = str(item.get("delta_materiality", "")).strip()
        if not reference or not overlap or not delta:
            raise ValueError(f"paper_claim_map relation {relation_index} fields must be non-empty")
        if delta_materiality not in {"substantial", "unclear", "minor"}:
            raise ValueError("paper_claim_map delta_materiality must be substantial|unclear|minor")
        relations.append(
            {
                "reference": reference,
                "overlap": overlap,
                "delta": delta,
                "delta_materiality": delta_materiality,
            }
        )

    closest_baseline = str(payload.get("closest_baseline", "")).strip()
    theorem_face_assessment = str(payload.get("theorem_face_assessment", "")).strip()
    baseline_delta = str(payload.get("baseline_delta", "")).strip()
    outsider_risk = str(payload.get("outsider_risk", "")).strip()
    if not closest_baseline or not theorem_face_assessment or not baseline_delta or not outsider_risk:
        raise ValueError("paper_claim_map summary fields must be non-empty")

    return {
        "problem_id": problem_id,
        "closest_baseline": closest_baseline,
        "relations": relations,
        "theorem_face_assessment": theorem_face_assessment,
        "baseline_delta": baseline_delta,
        "outsider_risk": outsider_risk,
    }


def validate_paper_claim_select_output(
    payload: dict[str, Any],
    *,
    expected_selection_id: str,
    known_problem_ids: list[str],
) -> dict[str, Any]:
    required_keys = {
        "selection_id",
        "selected_problem_id",
        "selection_note",
        "planning_focus",
        "assessments",
    }
    if set(payload.keys()) != required_keys:
        raise ValueError("paper_claim_select output keys mismatch required contract")

    selection_id = str(payload.get("selection_id", "")).strip()
    selected_problem_id = str(payload.get("selected_problem_id", "")).strip()
    selection_note = str(payload.get("selection_note", "")).strip()
    planning_focus = str(payload.get("planning_focus", "")).strip()
    raw_assessments = payload.get("assessments", [])
    if selection_id != expected_selection_id:
        raise ValueError("paper_claim_select selection_id does not match request")
    if not selected_problem_id or not selection_note or not planning_focus:
        raise ValueError("paper_claim_select core fields must be non-empty")
    if not isinstance(raw_assessments, list) or not raw_assessments:
        raise ValueError("paper_claim_select assessments must be a non-empty array")
    known_problem_id_set = {str(item).strip() for item in known_problem_ids if str(item).strip()}
    if known_problem_id_set and selected_problem_id not in known_problem_id_set:
        raise ValueError("paper_claim_select selected_problem_id must refer to an input dossier")

    assessments: list[dict[str, Any]] = []
    seen_problem_ids: set[str] = set()
    selected_assessment_count = 0
    for assessment_index, item in enumerate(raw_assessments, start=1):
        if not isinstance(item, dict):
            raise ValueError("paper_claim_select assessments must contain only objects")
        if set(item.keys()) != {
            "problem_id",
            "paper_publishable_fit",
            "selected",
            "why_selected",
            "why_not_selected",
        }:
            raise ValueError(f"paper_claim_select assessment {assessment_index} keys mismatch required contract")
        problem_id = str(item.get("problem_id", "")).strip()
        paper_publishable_fit = str(item.get("paper_publishable_fit", "")).strip()
        selected = bool(item.get("selected", False))
        why_selected = str(item.get("why_selected", "")).strip()
        why_not_selected = str(item.get("why_not_selected", "")).strip()
        if not problem_id:
            raise ValueError(f"paper_claim_select assessment {assessment_index} fields must be non-empty")
        if paper_publishable_fit not in {"high", "medium", "low"}:
            raise ValueError("paper_claim_select paper_publishable_fit must be high|medium|low")
        if known_problem_id_set and problem_id not in known_problem_id_set:
            raise ValueError("paper_claim_select assessment problem_id must refer to an input dossier")
        if problem_id in seen_problem_ids:
            raise ValueError("paper_claim_select assessment problem_id values must be unique")
        seen_problem_ids.add(problem_id)
        if selected:
            selected_assessment_count += 1
            if not why_selected or why_not_selected:
                raise ValueError(
                    "paper_claim_select selected assessment must have why_selected only"
                )
            if problem_id != selected_problem_id:
                raise ValueError(
                    "paper_claim_select selected assessment must match selected_problem_id"
                )
        else:
            if not why_not_selected or why_selected:
                raise ValueError(
                    "paper_claim_select non-selected assessment must have why_not_selected only"
                )
        assessments.append(
            {
                "problem_id": problem_id,
                "paper_publishable_fit": paper_publishable_fit,
                "selected": selected,
                "why_selected": why_selected,
                "why_not_selected": why_not_selected,
            }
        )
    if known_problem_id_set and seen_problem_ids != known_problem_id_set:
        raise ValueError("paper_claim_select assessments must cover each input dossier exactly once")
    if selected_assessment_count != 1:
        raise ValueError("paper_claim_select assessments must mark exactly one selected dossier")

    return {
        "selection_id": selection_id,
        "selected_problem_id": selected_problem_id,
        "selection_note": selection_note,
        "planning_focus": planning_focus,
        "assessments": assessments,
    }


def validate_paper_claim_plan_output(
    payload: dict[str, Any],
    *,
    expected_plan_id: str,
    known_problem_ids: list[str],
) -> dict[str, Any]:
    required_keys = {
        "plan_id",
        "selected_problem_id",
        "headline",
        "package_strategy",
        "theorem_units",
        "formalization_order",
    }
    if set(payload.keys()) != required_keys:
        raise ValueError("paper_claim_plan output keys mismatch required contract")

    plan_id = str(payload.get("plan_id", "")).strip()
    selected_problem_id = str(payload.get("selected_problem_id", "")).strip()
    headline = str(payload.get("headline", "")).strip()
    package_strategy = str(payload.get("package_strategy", "")).strip()
    if plan_id != expected_plan_id:
        raise ValueError("paper_claim_plan plan_id does not match request")
    known_problem_id_set = {str(item).strip() for item in known_problem_ids if str(item).strip()}
    if known_problem_id_set and selected_problem_id not in known_problem_id_set:
        raise ValueError("paper_claim_plan selected_problem_id must refer to an input dossier")
    if not headline or not package_strategy:
        raise ValueError("paper_claim_plan core fields must be non-empty")

    def _string_list(value: Any, *, field_name: str) -> list[str]:
        if not isinstance(value, list):
            raise ValueError(f"paper_claim_plan {field_name} must be an array")
        return [str(item).strip() for item in value if str(item).strip()]

    raw_units = payload.get("theorem_units", [])
    if not isinstance(raw_units, list) or not raw_units:
        raise ValueError("paper_claim_plan theorem_units must be a non-empty array")
    theorem_units: list[dict[str, Any]] = []
    seen_unit_ids: set[str] = set()
    for unit_index, item in enumerate(raw_units, start=1):
        if not isinstance(item, dict):
            raise ValueError("paper_claim_plan theorem_units must contain only objects")
        if set(item.keys()) != {
            "unit_id",
            "role",
            "kind",
            "name_stem",
            "statement",
            "docstring_summary",
            "purpose",
            "uses_existing_results",
            "needs_new_ingredients",
            "proof_idea",
            "unlocks",
        }:
            raise ValueError(f"paper_claim_plan theorem_unit {unit_index} keys mismatch required contract")
        unit_id = str(item.get("unit_id", "")).strip()
        role = str(item.get("role", "")).strip()
        kind = str(item.get("kind", "")).strip()
        name_stem = str(item.get("name_stem", "")).strip()
        statement = str(item.get("statement", "")).strip()
        docstring_summary = str(item.get("docstring_summary", "")).strip()
        purpose = str(item.get("purpose", "")).strip()
        if not unit_id or not role or not kind or not name_stem or not statement or not docstring_summary or not purpose:
            raise ValueError(f"paper_claim_plan theorem_unit {unit_index} core fields must be non-empty")
        if kind not in {"lemma", "theorem", "definition", "equivalence"}:
            raise ValueError("paper_claim_plan theorem_unit kind must be lemma|theorem|definition|equivalence")
        if unit_id in seen_unit_ids:
            raise ValueError("paper_claim_plan theorem_unit ids must be unique")
        seen_unit_ids.add(unit_id)
        proof_idea = _string_list(item.get("proof_idea", []), field_name=f"theorem_unit_{unit_index}_proof_idea")
        if not proof_idea:
            raise ValueError("paper_claim_plan theorem_unit proof_idea must be non-empty")
        theorem_units.append(
            {
                "unit_id": unit_id,
                "role": role,
                "kind": kind,
                "name_stem": name_stem,
                "statement": statement,
                "docstring_summary": docstring_summary,
                "purpose": purpose,
                "uses_existing_results": _string_list(
                    item.get("uses_existing_results", []),
                    field_name=f"theorem_unit_{unit_index}_uses_existing_results",
                ),
                "needs_new_ingredients": _string_list(
                    item.get("needs_new_ingredients", []),
                    field_name=f"theorem_unit_{unit_index}_needs_new_ingredients",
                ),
                "proof_idea": proof_idea,
                "unlocks": _string_list(item.get("unlocks", []), field_name=f"theorem_unit_{unit_index}_unlocks"),
            }
        )
    unit_id_set = {str(item["unit_id"]) for item in theorem_units}
    for unit in theorem_units:
        if any(unlock not in unit_id_set for unlock in unit["unlocks"]):
            raise ValueError("paper_claim_plan theorem_unit unlocks must refer to known unit ids")
    formalization_order = _string_list(payload.get("formalization_order", []), field_name="formalization_order")
    if not formalization_order:
        raise ValueError("paper_claim_plan formalization_order must be non-empty")
    if set(formalization_order) != unit_id_set or len(formalization_order) != len(unit_id_set):
        raise ValueError("paper_claim_plan formalization_order must cover each theorem unit exactly once")

    return {
        "plan_id": plan_id,
        "selected_problem_id": selected_problem_id,
        "headline": headline,
        "package_strategy": package_strategy,
        "theorem_units": theorem_units,
        "formalization_order": formalization_order,
    }


def paper_claim_plan_id_for_problem(selected_problem_id: str) -> str:
    problem_id = str(selected_problem_id).strip()
    if not problem_id:
        return "paper_claim_plan"
    return f"paper_claim_plan_for_{problem_id}"


def request_paper_claim_retrieval(
    *,
    worker_settings: Any,
    retriever_prompt: str,
    dossier: dict[str, Any],
    current_iteration: int,
    guidance: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    _, _, materials = unpack_guidance_context(guidance)
    retrieval_materials = _build_paper_claim_dossier_retrieval_materials(dossier, materials)
    payload = {
        "problem_id": str(dossier["problem_id"]),
        "current_iteration": current_iteration,
        "dossier": dossier,
        "materials": retrieval_materials,
    }
    response, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="paper_claim_retrieve",
        system_prompt=retriever_prompt,
        payload=payload,
        metadata={
            "problem_id": str(dossier["problem_id"]),
            "paper_excerpt_count": len(retrieval_materials.get("paper_excerpt_context", [])),
        },
    )
    return validate_paper_claim_retrieval_output(response, expected_problem_id=str(dossier["problem_id"])), worker_meta


def request_paper_claim_mapping(
    *,
    worker_settings: Any,
    mapper_prompt: str,
    dossier: dict[str, Any],
    retrieval: dict[str, Any],
    current_iteration: int,
    guidance: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    _, _, materials = unpack_guidance_context(guidance)
    review_materials = _build_paper_claim_dossier_retrieval_materials(dossier, materials)
    payload = {
        "problem_id": str(dossier["problem_id"]),
        "current_iteration": current_iteration,
        "dossier": dossier,
        "retrieval": retrieval,
        "materials": review_materials,
    }
    response, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="paper_claim_map",
        system_prompt=mapper_prompt,
        payload=payload,
        metadata={
            "problem_id": str(dossier["problem_id"]),
            "paper_excerpt_count": len(review_materials.get("paper_excerpt_context", [])),
        },
    )
    return validate_paper_claim_mapping_output(response, expected_problem_id=str(dossier["problem_id"])), worker_meta


def request_paper_claim_select(
    *,
    worker_settings: Any,
    selector_prompt: str,
    selection_id: str,
    dossier_packages: list[dict[str, Any]],
    current_iteration: int,
) -> tuple[dict[str, Any], dict[str, Any]]:
    payload = {
        "selection_id": selection_id,
        "current_iteration": current_iteration,
        "dossier_packages": dossier_packages,
    }
    response, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="paper_claim_select",
        system_prompt=selector_prompt,
        payload=payload,
        metadata={"selection_id": selection_id, "dossier_count": len(dossier_packages)},
    )
    return (
        validate_paper_claim_select_output(
            response,
            expected_selection_id=selection_id,
            known_problem_ids=[str(item.get("problem_id", "")).strip() for item in dossier_packages],
        ),
        worker_meta,
    )


def request_paper_claim_plan(
    *,
    worker_settings: Any,
    planner_prompt: str,
    plan_id: str,
    selected_dossier_package: dict[str, Any],
    selection: dict[str, Any],
    derived_entries: list[dict[str, str]],
    current_iteration: int,
    guidance: dict[str, Any],
    previous_plan: dict[str, Any] | None = None,
    completed_unit_ids: list[str] | None = None,
    refuted_unit_ids: list[str] | None = None,
    refutation_notes: str = "",
) -> tuple[dict[str, Any], dict[str, Any]]:
    theory_state, _, _ = unpack_guidance_context(guidance)
    payload = {
        "plan_id": plan_id,
        "current_iteration": current_iteration,
        "selected_dossier_package": selected_dossier_package,
        "selection": selection,
        "derived_theorems": [
            {
                "name": str(entry.get("name", "")),
                "statement": str(entry.get("statement", "")),
            }
            for entry in derived_entries
        ],
        "theory_state": _build_paper_claim_conceptual_theory_state(theory_state),
        "previous_plan": dict(previous_plan or {}),
        "completed_unit_ids": [str(item).strip() for item in (completed_unit_ids or []) if str(item).strip()],
        "refuted_unit_ids": [str(item).strip() for item in (refuted_unit_ids or []) if str(item).strip()],
        "refutation_notes": str(refutation_notes).strip(),
    }
    response, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="paper_claim_plan",
        system_prompt=planner_prompt,
        payload=payload,
        metadata={
            "plan_id": plan_id,
            "problem_id": str(selected_dossier_package.get("problem_id", "")).strip(),
        },
    )
    return (
        validate_paper_claim_plan_output(
            response,
            expected_plan_id=plan_id,
            known_problem_ids=[str(selected_dossier_package.get("problem_id", "")).strip()],
        ),
        worker_meta,
    )


def build_formalization_target_from_plan(plan: dict[str, Any]) -> dict[str, Any]:
    formalization_order = [str(item).strip() for item in plan.get("formalization_order", []) if str(item).strip()]
    theorem_units = {
        str(item.get("unit_id", "")).strip(): item
        for item in plan.get("theorem_units", [])
        if isinstance(item, dict) and str(item.get("unit_id", "")).strip()
    }
    if not formalization_order:
        raise ValueError("paper_claim_plan formalization_order must be non-empty before formalization")
    headline_unit_id = ""
    for unit_id in formalization_order:
        unit = theorem_units.get(unit_id)
        if isinstance(unit, dict) and str(unit.get("role", "")).strip() == "headline_theorem":
            headline_unit_id = unit_id
            break
    if not headline_unit_id:
        headline_unit_id = formalization_order[-1]
    headline_unit = theorem_units.get(headline_unit_id)
    if headline_unit is None:
        raise ValueError("paper_claim_plan headline formalization unit is missing from theorem_units")
    proof_idea = [str(item).strip() for item in headline_unit.get("proof_idea", []) if str(item).strip()]
    return {
        "candidate_id": str(plan["plan_id"]),
        "headline_unit_id": headline_unit_id,
        "statement": str(headline_unit["statement"]),
        "theorem_name_stem": str(headline_unit["name_stem"]),
        "docstring_summary": str(headline_unit["docstring_summary"]),
        "rationale": "\n".join(proof_idea) if proof_idea else str(headline_unit.get("purpose", "")),
        "supporting_theorems": list(headline_unit.get("uses_existing_results", [])),
        "missing_lemmas": list(headline_unit.get("needs_new_ingredients", [])),
        "source_problem_ids": [str(plan["selected_problem_id"])],
        "headline_kind": str(headline_unit["kind"]),
        "formalization_order": formalization_order,
        "theorem_units": theorem_units,
    }


def validate_paper_claim_codex_prove_output(payload: dict[str, Any]) -> dict[str, Any]:
    required_keys = {
        "status",
        "current_focus_unit_id",
        "completed_unit_ids",
        "refuted_unit_ids",
        "final_theorem_name",
        "final_statement",
        "helper_theorems",
        "verify_success",
        "error_excerpt",
        "notes",
    }
    if set(payload.keys()) != required_keys:
        raise ValueError("paper_claim_codex_prove output keys mismatch required contract")

    status = str(payload.get("status", "")).strip()
    current_focus_unit_id = str(payload.get("current_focus_unit_id", "")).strip()
    final_theorem_name = str(payload.get("final_theorem_name", "")).strip()
    final_statement = str(payload.get("final_statement", "")).strip()
    completed_unit_ids_value = payload.get("completed_unit_ids", [])
    refuted_unit_ids_value = payload.get("refuted_unit_ids", [])
    helper_theorems_value = payload.get("helper_theorems", [])
    verify_success = payload.get("verify_success")
    error_excerpt = str(payload.get("error_excerpt", "")).strip()
    notes = str(payload.get("notes", "")).strip()

    if status not in {"ok", "blocked", "timeout"}:
        raise ValueError("paper_claim_codex_prove status must be ok|blocked|timeout")
    if not isinstance(completed_unit_ids_value, list):
        raise ValueError("paper_claim_codex_prove completed_unit_ids must be an array")
    if not isinstance(refuted_unit_ids_value, list):
        raise ValueError("paper_claim_codex_prove refuted_unit_ids must be an array")
    if not isinstance(helper_theorems_value, list):
        raise ValueError("paper_claim_codex_prove helper_theorems must be an array")
    if not isinstance(verify_success, bool):
        raise ValueError("paper_claim_codex_prove verify_success must be a boolean")
    if not notes:
        raise ValueError("paper_claim_codex_prove notes must be non-empty")
    if status == "ok":
        if not final_theorem_name or not final_statement:
            raise ValueError("paper_claim_codex_prove ok requires final_theorem_name and final_statement")
        if not verify_success:
            raise ValueError("paper_claim_codex_prove ok requires verify_success=true")
        if not current_focus_unit_id:
            raise ValueError("paper_claim_codex_prove ok requires current_focus_unit_id")

    completed_unit_ids: list[str] = []
    for raw_item in completed_unit_ids_value:
        item = str(raw_item).strip()
        if item and item not in completed_unit_ids:
            completed_unit_ids.append(item)

    refuted_unit_ids: list[str] = []
    for raw_item in refuted_unit_ids_value:
        item = str(raw_item).strip()
        if item and item not in refuted_unit_ids:
            refuted_unit_ids.append(item)
    if set(completed_unit_ids) & set(refuted_unit_ids):
        raise ValueError("paper_claim_codex_prove completed_unit_ids and refuted_unit_ids must be disjoint")
    if refuted_unit_ids and not verify_success:
        raise ValueError("paper_claim_codex_prove refuted_unit_ids require verify_success=true")
    if status == "ok" and current_focus_unit_id not in completed_unit_ids:
        raise ValueError("paper_claim_codex_prove ok requires current_focus_unit_id in completed_unit_ids")

    helper_theorems: list[str] = []
    for raw_item in helper_theorems_value:
        item = str(raw_item).strip()
        if item and item not in helper_theorems:
            helper_theorems.append(item)

    return {
        "status": status,
        "current_focus_unit_id": current_focus_unit_id,
        "completed_unit_ids": completed_unit_ids,
        "refuted_unit_ids": refuted_unit_ids,
        "final_theorem_name": final_theorem_name,
        "final_statement": final_statement,
        "helper_theorems": helper_theorems,
        "verify_success": verify_success,
        "error_excerpt": error_excerpt,
        "notes": notes,
    }


def request_paper_claim_codex_prove(
    *,
    worker_settings: Any,
    prove_prompt: str,
    selected_problem_id: str,
    plan_id: str,
    current_unit: dict[str, Any],
    current_focus_unit_id: str,
    completed_unit_ids: list[str],
    headline_unit_id: str,
    selected_dossier_package: dict[str, Any],
    paper_claim_plan: dict[str, Any],
    scratch_file: Path,
    derived_file: Path,
    theory_context: str,
    current_iteration: int,
) -> tuple[dict[str, Any], dict[str, Any]]:
    payload = {
        "selected_problem_id": selected_problem_id,
        "plan_id": plan_id,
        "current_focus_unit_id": current_focus_unit_id,
        "headline_unit_id": headline_unit_id,
        "completed_unit_ids": list(completed_unit_ids),
        "theorem_name_hint": f"paper_claim_{str(current_unit.get('name_stem', '')).strip()}",
        "statement_hint": str(current_unit.get("statement", "")).strip(),
        "docstring_summary": str(current_unit.get("docstring_summary", "")).strip(),
        "rationale": "\n".join(
            str(item).strip() for item in current_unit.get("proof_idea", []) if str(item).strip()
        )
        or str(current_unit.get("purpose", "")).strip(),
        "supporting_theorems": list(current_unit.get("uses_existing_results", [])),
        "missing_lemmas": list(current_unit.get("needs_new_ingredients", [])),
        "scratch_file": str(scratch_file),
        "derived_file": str(derived_file),
        "selected_dossier_package": selected_dossier_package,
        "paper_claim_plan": paper_claim_plan,
        "theory_context": theory_context,
        "current_iteration": current_iteration,
    }
    response, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="paper_claim_codex_prove",
        system_prompt=prove_prompt,
        payload=payload,
        metadata={
            "problem_id": selected_problem_id,
            "plan_id": plan_id,
            "current_focus_unit_id": current_focus_unit_id,
        },
    )
    return validate_paper_claim_codex_prove_output(response), worker_meta


def _scratch_contains_relevant_sorry(scratch_file: Path) -> bool:
    try:
        scratch_text = scratch_file.read_text(encoding="utf-8")
    except OSError:
        return False
    return bool(re.search(r"\bsorry\b", scratch_text))


def _verify_error_excerpt_from_payload(payload: dict[str, Any]) -> str:
    stderr = str(payload.get("stderr", "")).strip()
    if stderr:
        return stderr
    diagnostics = payload.get("diagnostics", [])
    if isinstance(diagnostics, list):
        return "\n".join(str(item).strip() for item in diagnostics if str(item).strip())
    return str(diagnostics).strip()


def run_paper_claim_session(
    *,
    worker_settings: Any,
    scratch_file: Path,
    derived_file: Path,
    derived_entries: list[dict[str, str]],
    data_dir: Path,
    base_theory_context: str,
    formalize_worker_settings: Any,
    paper_claim_selector_prompt_file: str,
    paper_claim_retriever_prompt_file: str,
    paper_claim_mapper_prompt_file: str,
    paper_claim_planner_prompt_file: str,
    paper_claim_codex_prove_prompt_file: str,
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
    paper_claim_retry_budget_sec: int | None,
    failure_threshold: int,
    phase_logs: bool,
    run_id: str,
    phase_attempts_path: Path | None,
    session_events_path: Path | None,
    state_lock: threading.Lock,
    derived_runtime_state: dict[str, Any],
    problem_design_core_extract_prompt_file: str = "prompts/problem_design/core_extract.md",
    problem_design_cluster_prompt_file: str = "prompts/problem_design/cluster.md",
    problem_design_contextualize_prompt_file: str = "prompts/problem_design/contextualize.md",
) -> dict[str, Any]:
    problem_design_core_extract_prompt = load_prompt_text(problem_design_core_extract_prompt_file)
    problem_design_cluster_prompt = load_prompt_text(problem_design_cluster_prompt_file)
    problem_design_contextualize_prompt = load_prompt_text(problem_design_contextualize_prompt_file)
    paper_claim_selector_prompt = load_prompt_text(paper_claim_selector_prompt_file)
    paper_claim_retriever_prompt = load_prompt_text(paper_claim_retriever_prompt_file)
    paper_claim_mapper_prompt = load_prompt_text(paper_claim_mapper_prompt_file)
    paper_claim_planner_prompt = load_prompt_text(paper_claim_planner_prompt_file)
    paper_claim_codex_prove_prompt = load_prompt_text(paper_claim_codex_prove_prompt_file)
    materials_sync_report: dict[str, Any] | None = None
    try:
        materials_sync_report = ensure_materials_cache_current(
            repo_root / "materials",
            fetch_missing=True,
            extract_downloads=True,
        )
    except Exception:
        materials_sync_report = None
    guidance = load_current_guidance(data_dir)
    search_budget_sec = paper_claim_retry_budget_sec
    if search_budget_sec is None:
        search_budget_sec = 900
    search_deadline = time.monotonic() + max(1, int(search_budget_sec))
    problem_design_inventory = _merge_problem_design_inventory_entries(derived_entries, derived_file)
    cluster_contexts, failed_stage, failed_error = run_problem_design_contextualization(
        worker_settings=worker_settings,
        guidance=guidance,
        derived_entries=problem_design_inventory,
        current_iteration=current_iteration,
        phase_logs=phase_logs,
        run_id=run_id,
        phase_attempts_path=phase_attempts_path,
        session_events_path=session_events_path,
        cluster_prompt=problem_design_cluster_prompt,
        contextualize_prompt=problem_design_contextualize_prompt,
    )
    if cluster_contexts is None:
        status = f"{failed_stage}_error" if failed_stage else "problem_design_contextualization_error"
        report = {
            "status": status,
            "processed": False,
            "verify_success": False,
            "error": failed_error,
            "problem_design_dossiers": [],
            "problem_design_cluster_dossiers": [],
            "paper_claim_dossier_packages": [],
            "paper_claim_plan": {},
            "selected_candidate": {},
        }
        if materials_sync_report is not None:
            report["materials_sync"] = materials_sync_report
        if session_events_path is not None:
            report["session_events_file"] = str(session_events_path)
        return report
    problem_design_dossiers, failed_stage, failed_error = build_problem_design_dossiers(
        worker_settings=worker_settings,
        guidance=guidance,
        cluster_contexts=cluster_contexts,
        current_iteration=current_iteration,
        phase_logs=phase_logs,
        run_id=run_id,
        phase_attempts_path=phase_attempts_path,
        session_events_path=session_events_path,
        core_extract_prompt=problem_design_core_extract_prompt,
    )
    if problem_design_dossiers is None:
        status = "problem_design_dossier_build_error"
        if failed_stage:
            status = f"{failed_stage}_error"
        report = {
            "status": status,
            "processed": False,
            "verify_success": False,
            "error": failed_error,
            "problem_design_dossiers": [],
            "problem_design_cluster_dossiers": cluster_contexts,
            "paper_claim_dossier_packages": [],
            "paper_claim_plan": {},
            "selected_candidate": {},
        }
        if materials_sync_report is not None:
            report["materials_sync"] = materials_sync_report
        if session_events_path is not None:
            report["session_events_file"] = str(session_events_path)
        return report

    dossier_packages: list[dict[str, Any]] = []
    for dossier in problem_design_dossiers:
        if time.monotonic() > search_deadline:
            failed_stage = "paper_claim_budget"
            failed_error = "paper claim planning budget exhausted before retrieval/map finished"
            break

        problem_id = str(dossier["problem_id"])
        _, _, retrieval_source_materials = unpack_guidance_context(guidance)
        retrieval_access_summary = _summarize_retrieval_source_access(
            _build_paper_claim_dossier_retrieval_materials(dossier, retrieval_source_materials)
        )

        emit_phase_log(
            phase_logs,
            "paper_claim_retrieve",
            iteration=current_iteration,
            problem_id=problem_id,
        )
        started_monotonic = time.monotonic()
        started_at = iso_timestamp_now()
        try:
            retrieval, _ = request_paper_claim_retrieval(
                worker_settings=worker_settings,
                retriever_prompt=paper_claim_retriever_prompt,
                dossier=dossier,
                current_iteration=current_iteration,
                guidance=guidance,
            )
        except (RuntimeError, ValueError) as exc:
            failed_stage = "paper_claim_retrieve"
            failed_error = str(exc)
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type="paper_claim_session",
                iteration=current_iteration,
                entity_id=problem_id,
                phase="paper_claim_retrieve",
                worker_task="paper_claim_retrieve",
                started_at=started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(started_monotonic),
                success=False,
                result="error",
                error=failed_error,
            )
            _append_paper_claim_session_event(
                session_events_path,
                event="paper_claim_retrieve_result",
                run_id=run_id,
                iteration=current_iteration,
                candidate_set_id=problem_id,
                payload={"status": "error", "error": failed_error},
            )
            break
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type="paper_claim_session",
            iteration=current_iteration,
            entity_id=problem_id,
            phase="paper_claim_retrieve",
            worker_task="paper_claim_retrieve",
            started_at=started_at,
            finished_at=iso_timestamp_now(),
            duration_ms=monotonic_duration_ms(started_monotonic),
            success=True,
            result="ok",
        )
        emit_phase_log(
            phase_logs,
            "paper_claim_retrieve_result",
            iteration=current_iteration,
            problem_id=problem_id,
            closest_item_count=len(retrieval["closest_items"]),
            direct_evidence_count=len(retrieval["directly_read_evidence"]),
            local_paper_access_count=len(retrieval_access_summary["paper_access"]),
            local_source_link_access_count=len(retrieval_access_summary["source_link_access"]),
        )
        _append_paper_claim_session_event(
            session_events_path,
            event="paper_claim_retrieve_result",
            run_id=run_id,
            iteration=current_iteration,
            candidate_set_id=problem_id,
            payload={"status": "ok", **retrieval, "source_access": retrieval_access_summary},
        )

        emit_phase_log(
            phase_logs,
            "paper_claim_map",
            iteration=current_iteration,
            problem_id=problem_id,
        )
        started_monotonic = time.monotonic()
        started_at = iso_timestamp_now()
        try:
            mapping, _ = request_paper_claim_mapping(
                worker_settings=worker_settings,
                mapper_prompt=paper_claim_mapper_prompt,
                dossier=dossier,
                retrieval=retrieval,
                current_iteration=current_iteration,
                guidance=guidance,
            )
        except (RuntimeError, ValueError) as exc:
            failed_stage = "paper_claim_map"
            failed_error = str(exc)
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type="paper_claim_session",
                iteration=current_iteration,
                entity_id=problem_id,
                phase="paper_claim_map",
                worker_task="paper_claim_map",
                started_at=started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(started_monotonic),
                success=False,
                result="error",
                error=failed_error,
            )
            _append_paper_claim_session_event(
                session_events_path,
                event="paper_claim_map_result",
                run_id=run_id,
                iteration=current_iteration,
                candidate_set_id=problem_id,
                payload={"status": "error", "error": failed_error},
            )
            break
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type="paper_claim_session",
            iteration=current_iteration,
            entity_id=problem_id,
            phase="paper_claim_map",
            worker_task="paper_claim_map",
            started_at=started_at,
            finished_at=iso_timestamp_now(),
            duration_ms=monotonic_duration_ms(started_monotonic),
            success=True,
            result="ok",
        )
        emit_phase_log(
            phase_logs,
            "paper_claim_map_result",
            iteration=current_iteration,
            problem_id=problem_id,
            relation_count=len(mapping["relations"]),
            closest_baseline=str(mapping["closest_baseline"]),
        )
        _append_paper_claim_session_event(
            session_events_path,
            event="paper_claim_map_result",
            run_id=run_id,
            iteration=current_iteration,
            candidate_set_id=problem_id,
            payload={"status": "ok", **mapping},
        )
        dossier_packages.append(
            {
                "problem_id": problem_id,
                "dossier": dossier,
                "retrieval": retrieval,
                "mapping": mapping,
            }
        )

    if failed_stage:
        return {
            "status": f"{failed_stage}_error" if failed_stage != "paper_claim_budget" else failed_stage,
            "processed": False,
            "verify_success": False,
            "error": failed_error,
            "problem_design_dossiers": problem_design_dossiers,
            "problem_design_cluster_dossiers": cluster_contexts,
            "paper_claim_dossier_packages": dossier_packages,
            "paper_claim_selection": {},
            "paper_claim_plan": {},
            "selected_candidate": {},
        }
    if not dossier_packages:
        return {
            "status": "paper_claim_retrieve_empty",
            "processed": False,
            "verify_success": False,
            "error": "no dossier packages available for planning",
            "problem_design_dossiers": problem_design_dossiers,
            "problem_design_cluster_dossiers": cluster_contexts,
            "paper_claim_dossier_packages": [],
            "paper_claim_selection": {},
            "paper_claim_plan": {},
            "selected_candidate": {},
        }

    selection_id = "paper_claim_select_01"
    emit_phase_log(
        phase_logs,
        "paper_claim_select",
        iteration=current_iteration,
        selection_id=selection_id,
        dossier_count=len(dossier_packages),
    )
    started_monotonic = time.monotonic()
    started_at = iso_timestamp_now()
    try:
        paper_claim_selection, _ = request_paper_claim_select(
            worker_settings=worker_settings,
            selector_prompt=paper_claim_selector_prompt,
            selection_id=selection_id,
            dossier_packages=dossier_packages,
            current_iteration=current_iteration,
        )
    except (RuntimeError, ValueError) as exc:
        failed_stage = "paper_claim_select"
        failed_error = str(exc)
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type="paper_claim_session",
            iteration=current_iteration,
            entity_id=selection_id,
            phase="paper_claim_select",
            worker_task="paper_claim_select",
            started_at=started_at,
            finished_at=iso_timestamp_now(),
            duration_ms=monotonic_duration_ms(started_monotonic),
            success=False,
            result="error",
            error=failed_error,
        )
        _append_paper_claim_session_event(
            session_events_path,
            event="paper_claim_select_result",
            run_id=run_id,
            iteration=current_iteration,
            candidate_set_id=selection_id,
            payload={"status": "error", "error": failed_error},
        )
        return {
            "status": "paper_claim_select_error",
            "processed": False,
            "verify_success": False,
            "error": failed_error,
            "problem_design_dossiers": problem_design_dossiers,
            "problem_design_cluster_dossiers": cluster_contexts,
            "paper_claim_dossier_packages": dossier_packages,
            "paper_claim_selection": {},
            "paper_claim_plan": {},
            "selected_candidate": {},
        }
    append_phase_attempt_record(
        phase_attempts_path,
        run_id=run_id,
        session_type="paper_claim_session",
        iteration=current_iteration,
        entity_id=selection_id,
        phase="paper_claim_select",
        worker_task="paper_claim_select",
        started_at=started_at,
        finished_at=iso_timestamp_now(),
        duration_ms=monotonic_duration_ms(started_monotonic),
        success=True,
        result="ok",
    )
    emit_phase_log(
        phase_logs,
        "paper_claim_select_result",
        iteration=current_iteration,
        selection_id=selection_id,
        selected_problem_id=str(paper_claim_selection["selected_problem_id"]),
    )
    _append_paper_claim_session_event(
        session_events_path,
        event="paper_claim_select_result",
        run_id=run_id,
        iteration=current_iteration,
        candidate_set_id=selection_id,
        payload={"status": "ok", **paper_claim_selection},
    )
    selected_problem_id = str(paper_claim_selection["selected_problem_id"])
    selected_dossier_package = next(
        item for item in dossier_packages if str(item.get("problem_id", "")).strip() == selected_problem_id
    )

    plan_id = paper_claim_plan_id_for_problem(selected_problem_id)
    emit_phase_log(
        phase_logs,
        "paper_claim_plan",
        iteration=current_iteration,
        plan_id=plan_id,
        selected_problem_id=selected_problem_id,
    )
    started_monotonic = time.monotonic()
    started_at = iso_timestamp_now()
    try:
        paper_claim_plan, _ = request_paper_claim_plan(
            worker_settings=worker_settings,
            planner_prompt=paper_claim_planner_prompt,
            plan_id=plan_id,
            selected_dossier_package=selected_dossier_package,
            selection=paper_claim_selection,
            derived_entries=derived_entries,
            current_iteration=current_iteration,
            guidance=guidance,
        )
    except (RuntimeError, ValueError) as exc:
        failed_stage = "paper_claim_plan"
        failed_error = str(exc)
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type="paper_claim_session",
            iteration=current_iteration,
            entity_id=plan_id,
            phase="paper_claim_plan",
            worker_task="paper_claim_plan",
            started_at=started_at,
            finished_at=iso_timestamp_now(),
            duration_ms=monotonic_duration_ms(started_monotonic),
            success=False,
            result="error",
            error=failed_error,
        )
        _append_paper_claim_session_event(
            session_events_path,
            event="paper_claim_plan_result",
            run_id=run_id,
            iteration=current_iteration,
            candidate_set_id=plan_id,
            payload={"status": "error", "error": failed_error},
        )
        return {
            "status": "paper_claim_plan_error",
            "processed": False,
            "verify_success": False,
            "error": failed_error,
            "problem_design_dossiers": problem_design_dossiers,
            "problem_design_cluster_dossiers": cluster_contexts,
            "paper_claim_dossier_packages": dossier_packages,
            "paper_claim_selection": paper_claim_selection,
            "paper_claim_plan": {},
            "selected_candidate": {},
        }
    append_phase_attempt_record(
        phase_attempts_path,
        run_id=run_id,
        session_type="paper_claim_session",
        iteration=current_iteration,
        entity_id=plan_id,
        phase="paper_claim_plan",
        worker_task="paper_claim_plan",
        started_at=started_at,
        finished_at=iso_timestamp_now(),
        duration_ms=monotonic_duration_ms(started_monotonic),
        success=True,
        result="ok",
    )
    emit_phase_log(
        phase_logs,
        "paper_claim_plan_result",
        iteration=current_iteration,
        plan_id=plan_id,
        selected_problem_id=str(paper_claim_plan["selected_problem_id"]),
        theorem_unit_count=len(list(paper_claim_plan.get("theorem_units", []))),
        first_formalization_unit_id=str(list(paper_claim_plan.get("formalization_order", [""]))[0]),
    )
    _append_paper_claim_session_event(
        session_events_path,
        event="paper_claim_plan_result",
        run_id=run_id,
        iteration=current_iteration,
        candidate_set_id=plan_id,
        payload={
            "status": "ok",
            **paper_claim_plan,
            "paper_claim_selection": paper_claim_selection,
            "selected_dossier_package": selected_dossier_package,
        },
    )

    selected_candidate = build_formalization_target_from_plan(paper_claim_plan)
    report = process_paper_claim_formalization_plan(
        candidate_id=str(selected_candidate["candidate_id"]),
        headline_unit_id=str(selected_candidate["headline_unit_id"]),
        selected_candidate=selected_candidate,
        scratch_file=scratch_file,
        derived_file=derived_file,
        derived_entries=derived_entries,
        data_dir=data_dir,
        base_theory_context=base_theory_context,
        formalize_worker_settings=formalize_worker_settings,
        worker_settings=worker_settings,
        prove_prompt=paper_claim_codex_prove_prompt,
        selected_problem_id=selected_problem_id,
        plan_id=plan_id,
        selection=paper_claim_selection,
        selected_dossier_package=selected_dossier_package,
        paper_claim_plan=paper_claim_plan,
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
        failure_threshold=failure_threshold,
        phase_logs=phase_logs,
        run_id=run_id,
        phase_attempts_path=phase_attempts_path,
        session_events_path=session_events_path,
        theory_state_history_path=(
            (phase_attempts_path.parent if phase_attempts_path is not None else paper_claim_run_dir(data_dir, run_id))
            / "theory_state_history.jsonl"
        ),
        state_lock=state_lock,
        derived_runtime_state=derived_runtime_state,
        guidance=guidance,
        planner_prompt=paper_claim_planner_prompt,
    )
    report["selected_candidate"] = selected_candidate
    report["selection_summary"] = str(paper_claim_selection["selection_note"])
    report["suggested_statement"] = str(selected_candidate["statement"])
    report["suggested_rationale"] = str(selected_candidate["rationale"])
    report["source_problem_ids"] = list(selected_candidate["source_problem_ids"])
    report["problem_design_dossiers"] = problem_design_dossiers
    report["problem_design_cluster_dossiers"] = cluster_contexts
    report["paper_claim_dossier_packages"] = dossier_packages
    report["paper_claim_selection"] = paper_claim_selection
    report["paper_claim_plan"] = paper_claim_plan
    if materials_sync_report is not None:
        report["materials_sync"] = materials_sync_report
    if session_events_path is not None:
        report["session_events_file"] = str(session_events_path)
    return report


def resume_paper_claim_session_from_plan_event(
    *,
    resume_session_events_path: Path,
    resume_plan_id: str,
    worker_settings: Any,
    scratch_file: Path,
    derived_file: Path,
    derived_entries: list[dict[str, str]],
    data_dir: Path,
    base_theory_context: str,
    formalize_worker_settings: Any,
    paper_claim_planner_prompt_file: str,
    paper_claim_codex_prove_prompt_file: str,
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
    failure_threshold: int,
    phase_logs: bool,
    run_id: str,
    phase_attempts_path: Path | None,
    session_events_path: Path | None,
    state_lock: threading.Lock,
    derived_runtime_state: dict[str, Any],
) -> dict[str, Any]:
    paper_claim_planner_prompt = load_prompt_text(paper_claim_planner_prompt_file)
    paper_claim_codex_prove_prompt = load_prompt_text(paper_claim_codex_prove_prompt_file)
    guidance = load_current_guidance(data_dir)
    resume_context = load_paper_claim_resume_context_from_session_events(
        session_events_path=resume_session_events_path,
        plan_id=resume_plan_id,
    )
    paper_claim_plan = dict(resume_context["paper_claim_plan"])
    paper_claim_selection = dict(resume_context["paper_claim_selection"])
    selected_dossier_package = dict(resume_context["selected_dossier_package"])
    selected_problem_id = str(resume_context["selected_problem_id"])

    if session_events_path is not None:
        _append_paper_claim_session_event(
            session_events_path,
            event="paper_claim_resume_from_plan",
            run_id=run_id,
            iteration=current_iteration,
            candidate_set_id=str(paper_claim_plan.get("plan_id", "")),
            payload={
                "resume_source_session_events_file": str(resume_session_events_path),
                "resumed_plan_id": str(paper_claim_plan.get("plan_id", "")),
                "selected_problem_id": selected_problem_id,
            },
        )

    selected_candidate = build_formalization_target_from_plan(paper_claim_plan)
    report = process_paper_claim_formalization_plan(
        candidate_id=str(selected_candidate["candidate_id"]),
        headline_unit_id=str(selected_candidate["headline_unit_id"]),
        selected_candidate=selected_candidate,
        scratch_file=scratch_file,
        derived_file=derived_file,
        derived_entries=derived_entries,
        data_dir=data_dir,
        base_theory_context=base_theory_context,
        formalize_worker_settings=formalize_worker_settings,
        worker_settings=worker_settings,
        prove_prompt=paper_claim_codex_prove_prompt,
        selected_problem_id=selected_problem_id,
        plan_id=str(paper_claim_plan.get("plan_id", "")),
        selection=paper_claim_selection,
        selected_dossier_package=selected_dossier_package,
        paper_claim_plan=paper_claim_plan,
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
        failure_threshold=failure_threshold,
        phase_logs=phase_logs,
        run_id=run_id,
        phase_attempts_path=phase_attempts_path,
        session_events_path=session_events_path,
        theory_state_history_path=(
            (phase_attempts_path.parent if phase_attempts_path is not None else paper_claim_run_dir(data_dir, run_id))
            / "theory_state_history.jsonl"
        ),
        state_lock=state_lock,
        derived_runtime_state=derived_runtime_state,
        guidance=guidance,
        planner_prompt=paper_claim_planner_prompt,
    )
    report["selected_candidate"] = selected_candidate
    report["selection_summary"] = str(paper_claim_selection.get("selection_note", ""))
    report["suggested_statement"] = str(selected_candidate["statement"])
    report["suggested_rationale"] = str(selected_candidate["rationale"])
    report["source_problem_ids"] = list(selected_candidate["source_problem_ids"])
    report["problem_design_dossiers"] = []
    report["problem_design_cluster_dossiers"] = []
    report["paper_claim_dossier_packages"] = [selected_dossier_package]
    report["paper_claim_selection"] = paper_claim_selection
    report["paper_claim_plan"] = paper_claim_plan
    report["resume_source_session_events_file"] = str(resume_session_events_path)
    if session_events_path is not None:
        report["session_events_file"] = str(session_events_path)
    return report


def _normalize_known_unit_ids(value: Any, *, known_unit_ids: set[str]) -> list[str]:
    if not isinstance(value, list):
        return []
    normalized: list[str] = []
    for raw_item in value:
        item = str(raw_item).strip()
        if item and item in known_unit_ids and item not in normalized:
            normalized.append(item)
    return normalized


def _commit_verified_paper_claim_progress(
    *,
    scratch_file: Path,
    scratch_text: str | None,
    derived_file: Path,
    derived_entries: list[dict[str, str]],
    docstring_summary: str,
    data_dir: Path,
    derived_runtime_state: dict[str, Any],
    run_id: str,
    current_iteration: int,
    skip_verify: bool,
    state_lock: threading.Lock,
) -> str:
    target_scratch_path = scratch_file
    temp_scratch_path: Path | None = None
    if scratch_text is not None:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            suffix=".lean",
            delete=False,
            dir=str(scratch_file.parent),
        ) as handle:
            handle.write(scratch_text)
            temp_scratch_path = Path(handle.name)
        target_scratch_path = temp_scratch_path

    theorem_code = extract_theorem_code_from_scratch(target_scratch_path)
    if not theorem_code:
        if temp_scratch_path is not None:
            temp_scratch_path.unlink(missing_ok=True)
        return ""
    try:
        with state_lock:
            return commit_verified_theorem_and_generation(
                scratch_path=target_scratch_path,
                derived_file=derived_file,
                derived_entries=derived_entries,
                docstring=docstring_summary,
                data_dir=data_dir,
                derived_runtime_state=derived_runtime_state,
                run_id=run_id,
                current_iteration=current_iteration,
                rebuild_derived=not skip_verify,
            )
    finally:
        if temp_scratch_path is not None:
            temp_scratch_path.unlink(missing_ok=True)


def process_paper_claim_formalization_plan(
    *,
    candidate_id: str,
    headline_unit_id: str,
    selected_candidate: dict[str, Any],
    scratch_file: Path,
    derived_file: Path,
    derived_entries: list[dict[str, str]],
    data_dir: Path,
    base_theory_context: str,
    formalize_worker_settings: Any,
    worker_settings: Any,
    prove_prompt: str,
    selected_problem_id: str,
    plan_id: str,
    selection: dict[str, Any],
    selected_dossier_package: dict[str, Any],
    paper_claim_plan: dict[str, Any],
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
    failure_threshold: int,
    phase_logs: bool,
    run_id: str,
    phase_attempts_path: Path | None,
    session_events_path: Path | None,
    theory_state_history_path: Path,
    state_lock: threading.Lock,
    derived_runtime_state: dict[str, Any],
    guidance: dict[str, Any],
    planner_prompt: str,
) -> dict[str, Any]:
    current_iteration_full_logs: list[dict[str, Any]] = []
    headline_statement = str(selected_candidate.get("statement", "")).strip()
    headline_theorem_name = f"paper_claim_{str(selected_candidate.get('theorem_name_stem', '')).strip()}"
    if not headline_statement or not headline_theorem_name or not headline_unit_id:
        return {
            "processed": False,
            "candidate_id": candidate_id,
            "status": "blocked",
            "verify_success": False,
        }

    completed_unit_ids: list[str] = []
    plan_revisions: list[dict[str, Any]] = [dict(paper_claim_plan)]
    active_plan = dict(paper_claim_plan)
    total_replan_count = 0
    committed_theorem_code = ""
    last_notes = ""
    last_helper_theorems: list[str] = []
    last_supporting_theorems: list[str] = list(selected_candidate.get("supporting_theorems", []))
    last_missing_lemmas: list[str] = list(selected_candidate.get("missing_lemmas", []))
    last_verified_scratch_text = ""
    last_verified_docstring_summary = ""
    final_theorem_name = headline_theorem_name
    final_statement = headline_statement
    scratch_file.parent.mkdir(parents=True, exist_ok=True)
    scratch_file.write_text(SCRATCH_TEMPLATE, encoding="utf-8")

    def flush_pending_verified_progress(*, fallback_docstring_summary: str) -> str:
        nonlocal committed_theorem_code
        if not last_verified_scratch_text or committed_theorem_code:
            return committed_theorem_code
        committed_theorem_code = _commit_verified_paper_claim_progress(
            scratch_file=scratch_file,
            scratch_text=last_verified_scratch_text,
            derived_file=derived_file,
            derived_entries=derived_entries,
            docstring_summary=last_verified_docstring_summary or fallback_docstring_summary,
            data_dir=data_dir,
            derived_runtime_state=derived_runtime_state,
            run_id=run_id,
            current_iteration=current_iteration,
            skip_verify=skip_verify,
            state_lock=state_lock,
        )
        return committed_theorem_code

    while True:
        formalization_order = [
            str(item).strip()
            for item in active_plan.get("formalization_order", [])
            if str(item).strip()
        ]
        theorem_units = {
            str(item.get("unit_id", "")).strip(): item
            for item in active_plan.get("theorem_units", [])
            if isinstance(item, dict) and str(item.get("unit_id", "")).strip()
        }
        known_unit_ids = set(formalization_order)
        if headline_unit_id not in known_unit_ids:
            for unit_id in formalization_order:
                unit = theorem_units.get(unit_id)
                if isinstance(unit, dict) and str(unit.get("role", "")).strip() == "headline_theorem":
                    headline_unit_id = unit_id
                    break
            if headline_unit_id not in known_unit_ids and formalization_order:
                headline_unit_id = formalization_order[-1]

        remaining_unit_ids = [unit_id for unit_id in formalization_order if unit_id not in completed_unit_ids]
        if headline_unit_id in completed_unit_ids:
            break
        if not remaining_unit_ids:
            break

        current_focus_unit_id = remaining_unit_ids[0]
        current_unit = theorem_units.get(current_focus_unit_id)
        if not isinstance(current_unit, dict):
            return {
                "processed": True,
                "candidate_id": candidate_id,
                "status": "blocked",
                "verify_success": False,
                "verify_error_excerpt": "paper_claim_plan current formalization unit is missing from theorem_units",
                "notes": last_notes,
                "completed_unit_ids": list(completed_unit_ids),
                "headline_unit_id": headline_unit_id,
                "refuted_unit_ids": [],
                "plan_revisions": plan_revisions,
                "replan_count": total_replan_count,
            }

        statement = str(current_unit.get("statement", "")).strip()
        theorem_name = f"paper_claim_{str(current_unit.get('name_stem', '')).strip()}"
        docstring_summary = str(current_unit.get("docstring_summary", "")).strip()
        rationale = "\n".join(str(item).strip() for item in current_unit.get("proof_idea", []) if str(item).strip())
        supporting_theorems = [str(item).strip() for item in current_unit.get("uses_existing_results", []) if str(item).strip()]
        missing_lemmas = [str(item).strip() for item in current_unit.get("needs_new_ingredients", []) if str(item).strip()]

        theorem_context = build_problem_theory_context(base_theory_context, derived_entries, statement)
        emit_phase_log(
            phase_logs,
            "paper_claim_codex_prove",
            iteration=current_iteration,
            candidate_id=candidate_id,
            theorem_name=theorem_name,
            selected_problem_id=selected_problem_id,
            plan_id=str(active_plan.get("plan_id", plan_id)),
            current_focus_unit_id=current_focus_unit_id,
            completed_unit_ids=list(completed_unit_ids),
            headline_unit_id=headline_unit_id,
        )
        started_monotonic = time.monotonic()
        started_at = iso_timestamp_now()
        try:
            codex_result, _ = request_paper_claim_codex_prove(
                worker_settings=formalize_worker_settings,
                prove_prompt=prove_prompt,
                selected_problem_id=selected_problem_id,
                plan_id=str(active_plan.get("plan_id", plan_id)),
                current_unit=current_unit,
                current_focus_unit_id=current_focus_unit_id,
                completed_unit_ids=completed_unit_ids,
                headline_unit_id=headline_unit_id,
                selected_dossier_package=selected_dossier_package,
                paper_claim_plan=active_plan,
                scratch_file=scratch_file,
                derived_file=derived_file,
                theory_context=theorem_context,
                current_iteration=current_iteration,
            )
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type="paper_claim_session",
                iteration=current_iteration,
                entity_id=candidate_id,
                phase="paper_claim_codex_prove",
                worker_task="paper_claim_codex_prove",
                started_at=started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(started_monotonic),
                success=True,
                result=str(codex_result.get("status", "ok")),
            )
        except (RuntimeError, ValueError) as exc:
            verify_error_excerpt = str(exc)
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type="paper_claim_session",
                iteration=current_iteration,
                entity_id=candidate_id,
                phase="paper_claim_codex_prove",
                worker_task="paper_claim_codex_prove",
                started_at=started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(started_monotonic),
                success=False,
                result="error",
                error=verify_error_excerpt,
            )
            emit_phase_log(
                phase_logs,
                "paper_claim_codex_prove_result",
                iteration=current_iteration,
                candidate_id=candidate_id,
                theorem_name=theorem_name,
                status="error",
                error=verify_error_excerpt,
                current_focus_unit_id=current_focus_unit_id,
            )
            followup_refresh = _store_paper_claim_followups(
                data_dir=data_dir,
                theorem_name=theorem_name,
                statement=statement,
                rationale=rationale,
                verify_error_excerpt=verify_error_excerpt,
                missing_lemmas=missing_lemmas,
                intermediate_lemmas=[],
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
            flush_pending_verified_progress(fallback_docstring_summary=docstring_summary)
            return {
                "processed": True,
                "candidate_id": candidate_id,
                "status": "blocked",
                "verify_success": False,
                "verify_error_excerpt": verify_error_excerpt,
                "notes": "",
                "followup_candidates": list(followup_refresh.get("followup_candidates", [])),
                "stored_expand_rows": list(followup_refresh.get("stored_expand_rows", [])),
                "priority_refresh_ran": bool(followup_refresh.get("priority_refresh_ran", False)),
                "priority_refresh_error": str(followup_refresh.get("priority_refresh_error", "")),
                "completed_unit_ids": list(completed_unit_ids),
                "headline_unit_id": headline_unit_id,
                "refuted_unit_ids": [],
                "plan_revisions": plan_revisions,
                "replan_count": total_replan_count,
                "theorem_code": committed_theorem_code,
            }

        emit_phase_log(
            phase_logs,
            "paper_claim_codex_prove_result",
            iteration=current_iteration,
            candidate_id=candidate_id,
            theorem_name=theorem_name,
            status=str(codex_result.get("status", "")),
            final_theorem_name=str(codex_result.get("final_theorem_name", "")),
            current_focus_unit_id=current_focus_unit_id,
        )

        verify_error_excerpt = str(codex_result.get("error_excerpt", "")).strip()
        notes = str(codex_result.get("notes", "")).strip()
        helper_theorems = [str(item).strip() for item in codex_result.get("helper_theorems", []) if str(item).strip()]
        normalized_completed = _normalize_known_unit_ids(
            codex_result.get("completed_unit_ids", []),
            known_unit_ids=known_unit_ids,
        )
        normalized_refuted = _normalize_known_unit_ids(
            codex_result.get("refuted_unit_ids", []),
            known_unit_ids=known_unit_ids,
        )
        final_theorem_name = str(codex_result.get("final_theorem_name", "")).strip() or theorem_name
        final_statement = str(codex_result.get("final_statement", "")).strip() or statement
        if skip_verify:
            verify_success = bool(codex_result.get("verify_success", False)) and not _scratch_contains_relevant_sorry(scratch_file)
        else:
            verify_payload = verify_scratch(candidate_id, "proof", scratch_file, timeout_sec=verify_timeout_sec)
            verify_success = bool(verify_payload.get("success", False)) and not _scratch_contains_relevant_sorry(scratch_file)
            if not verify_success and not verify_error_excerpt:
                verify_error_excerpt = _verify_error_excerpt_from_payload(verify_payload)

        if verify_success:
            last_verified_scratch_text = scratch_file.read_text(encoding="utf-8")
            last_verified_docstring_summary = docstring_summary
        emit_phase_log(
            phase_logs,
            "paper_claim_unit_result",
            iteration=current_iteration,
            candidate_id=candidate_id,
            theorem_name=final_theorem_name,
            current_focus_unit_id=current_focus_unit_id,
            verify_success=verify_success,
            completed_unit_ids=normalized_completed,
            refuted_unit_ids=normalized_refuted,
            error_excerpt=verify_error_excerpt,
            appended_to_derived=False,
        )
        _append_paper_claim_session_event(
            session_events_path,
            event="paper_claim_unit_result",
            run_id=run_id,
            iteration=current_iteration,
            candidate_set_id=candidate_id,
            payload={
                "plan_id": str(active_plan.get("plan_id", plan_id)),
                "problem_id": selected_problem_id,
                "candidate_id": candidate_id,
                "current_focus_unit_id": current_focus_unit_id,
                "headline_unit_id": headline_unit_id,
                "status": str(codex_result.get("status", "")),
                "verify_success": verify_success,
                "completed_unit_ids": normalized_completed,
                "refuted_unit_ids": normalized_refuted,
                "final_theorem_name": final_theorem_name,
                "appended_to_derived": False,
            },
        )
        last_notes = notes
        last_helper_theorems = helper_theorems
        last_supporting_theorems = supporting_theorems
        last_missing_lemmas = missing_lemmas

        if verify_success and current_focus_unit_id in normalized_completed:
            if current_focus_unit_id not in completed_unit_ids:
                completed_unit_ids.append(current_focus_unit_id)
            if headline_unit_id in completed_unit_ids:
                break
            continue

        if verify_success and normalized_refuted:
            total_replan_count += 1
            emit_phase_log(
                phase_logs,
                "paper_claim_plan_rebuild",
                iteration=current_iteration,
                candidate_id=candidate_id,
                plan_id=str(active_plan.get("plan_id", plan_id)),
                current_focus_unit_id=current_focus_unit_id,
                refuted_unit_ids=normalized_refuted,
            )
            _append_paper_claim_session_event(
                session_events_path,
                event="paper_claim_plan_rebuild",
                run_id=run_id,
                iteration=current_iteration,
                candidate_set_id=candidate_id,
                payload={
                    "plan_id": str(active_plan.get("plan_id", plan_id)),
                    "problem_id": selected_problem_id,
                    "candidate_id": candidate_id,
                    "current_focus_unit_id": current_focus_unit_id,
                    "completed_unit_ids": list(completed_unit_ids),
                    "refuted_unit_ids": normalized_refuted,
                    "notes": notes,
                },
            )
            try:
                replanned_plan, _ = request_paper_claim_plan(
                    worker_settings=worker_settings,
                    planner_prompt=planner_prompt,
                    plan_id=plan_id,
                    selected_dossier_package=selected_dossier_package,
                    selection={
                        **selection,
                        "selection_note": "\n".join(
                            part
                            for part in (
                                str(selection.get("selection_note", "")).strip(),
                                "Rebuild the package only because a verified refutation or hard contradiction invalidated part of the current plan.",
                            )
                            if part
                        ),
                    },
                    derived_entries=derived_entries,
                    current_iteration=current_iteration,
                    guidance=guidance,
                    previous_plan=active_plan,
                    completed_unit_ids=completed_unit_ids,
                    refuted_unit_ids=normalized_refuted,
                    refutation_notes=notes or verify_error_excerpt,
                )
            except (RuntimeError, ValueError) as exc:
                verify_error_excerpt = str(exc)
                followup_refresh = _store_paper_claim_followups(
                    data_dir=data_dir,
                    theorem_name=final_theorem_name,
                    statement=final_statement,
                    rationale="\n".join(part for part in (rationale, notes) if part.strip()),
                    verify_error_excerpt=verify_error_excerpt,
                    missing_lemmas=missing_lemmas,
                    intermediate_lemmas=helper_theorems,
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
                flush_pending_verified_progress(fallback_docstring_summary=docstring_summary)
                return {
                    "processed": True,
                    "candidate_id": candidate_id,
                    "status": "blocked",
                    "verify_success": verify_success,
                    "verify_error_excerpt": verify_error_excerpt,
                    "notes": notes,
                    "followup_candidates": list(followup_refresh.get("followup_candidates", [])),
                    "stored_expand_rows": list(followup_refresh.get("stored_expand_rows", [])),
                    "priority_refresh_ran": bool(followup_refresh.get("priority_refresh_ran", False)),
                    "priority_refresh_error": str(followup_refresh.get("priority_refresh_error", "")),
                    "completed_unit_ids": list(completed_unit_ids),
                    "headline_unit_id": headline_unit_id,
                    "refuted_unit_ids": normalized_refuted,
                    "plan_revisions": plan_revisions,
                    "replan_count": total_replan_count,
                    "theorem_code": committed_theorem_code,
                }
            if replanned_plan == active_plan:
                flush_pending_verified_progress(fallback_docstring_summary=docstring_summary)
                verify_error_excerpt = (
                    "paper_claim_plan rebuild returned the same plan after a verified refutation"
                )
                followup_refresh = _store_paper_claim_followups(
                    data_dir=data_dir,
                    theorem_name=final_theorem_name,
                    statement=final_statement,
                    rationale="\n".join(part for part in (rationale, notes) if part.strip()),
                    verify_error_excerpt=verify_error_excerpt,
                    missing_lemmas=missing_lemmas,
                    intermediate_lemmas=helper_theorems,
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
                    "verify_success": verify_success,
                    "verify_error_excerpt": verify_error_excerpt,
                    "notes": notes,
                    "followup_candidates": list(followup_refresh.get("followup_candidates", [])),
                    "stored_expand_rows": list(followup_refresh.get("stored_expand_rows", [])),
                    "priority_refresh_ran": bool(followup_refresh.get("priority_refresh_ran", False)),
                    "priority_refresh_error": str(followup_refresh.get("priority_refresh_error", "")),
                    "completed_unit_ids": list(completed_unit_ids),
                    "headline_unit_id": headline_unit_id,
                    "refuted_unit_ids": normalized_refuted,
                    "plan_revisions": plan_revisions,
                    "replan_count": total_replan_count,
                    "theorem_code": committed_theorem_code,
                }
            active_plan = replanned_plan
            plan_revisions.append(dict(replanned_plan))
            continue

        followup_refresh = _store_paper_claim_followups(
            data_dir=data_dir,
            theorem_name=final_theorem_name,
            statement=final_statement,
            rationale="\n".join(part for part in (rationale, notes) if part.strip()),
            verify_error_excerpt=verify_error_excerpt,
            missing_lemmas=missing_lemmas,
            intermediate_lemmas=helper_theorems,
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
        flush_pending_verified_progress(fallback_docstring_summary=docstring_summary)
        return {
            "processed": True,
            "candidate_id": candidate_id,
            "status": "blocked",
            "verify_success": verify_success,
            "verify_error_excerpt": verify_error_excerpt,
            "notes": notes,
            "followup_candidates": list(followup_refresh.get("followup_candidates", [])),
            "stored_expand_rows": list(followup_refresh.get("stored_expand_rows", [])),
            "priority_refresh_ran": bool(followup_refresh.get("priority_refresh_ran", False)),
            "priority_refresh_error": str(followup_refresh.get("priority_refresh_error", "")),
            "completed_unit_ids": list(completed_unit_ids),
            "headline_unit_id": headline_unit_id,
            "refuted_unit_ids": normalized_refuted,
            "plan_revisions": plan_revisions,
            "replan_count": total_replan_count,
            "theorem_code": committed_theorem_code,
            "theorem_name": final_theorem_name,
            "statement": final_statement,
            "helper_theorems": helper_theorems,
        }

    if headline_unit_id not in completed_unit_ids:
        flush_pending_verified_progress(
            fallback_docstring_summary=str(selected_candidate.get("docstring_summary", "")).strip()
        )
        verify_error_excerpt = "paper_claim_session exhausted the current plan before reaching the headline theorem"
        followup_refresh = _store_paper_claim_followups(
            data_dir=data_dir,
            theorem_name=final_theorem_name,
            statement=final_statement,
            rationale="\n".join(
                part for part in (str(selected_candidate.get("rationale", "")).strip(), last_notes) if part.strip()
            ),
            verify_error_excerpt=verify_error_excerpt,
            missing_lemmas=list(last_missing_lemmas),
            intermediate_lemmas=list(last_helper_theorems),
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
            "notes": last_notes,
            "followup_candidates": list(followup_refresh.get("followup_candidates", [])),
            "stored_expand_rows": list(followup_refresh.get("stored_expand_rows", [])),
            "priority_refresh_ran": bool(followup_refresh.get("priority_refresh_ran", False)),
            "priority_refresh_error": str(followup_refresh.get("priority_refresh_error", "")),
            "completed_unit_ids": list(completed_unit_ids),
            "headline_unit_id": headline_unit_id,
            "refuted_unit_ids": [],
            "plan_revisions": plan_revisions,
            "replan_count": total_replan_count,
            "theorem_code": committed_theorem_code,
            "theorem_name": final_theorem_name,
            "statement": final_statement,
            "helper_theorems": list(last_helper_theorems),
        }

    flush_pending_verified_progress(
        fallback_docstring_summary=str(selected_candidate.get("docstring_summary", "")).strip()
    )

    known_theorem_names = {
        str(entry.get("name", "")).strip()
        for entry in derived_entries
        if str(entry.get("name", "")).strip()
    }
    theorem_context = build_problem_theory_context(base_theory_context, derived_entries, final_statement)
    post_expand_candidates: list[dict[str, str]] = []
    post_expand_error = ""
    emit_phase_log(
        phase_logs,
        "post_theorem_expand",
        iteration=current_iteration,
        candidate_id=candidate_id,
        theorem_name=final_theorem_name,
    )
    post_expand_started_monotonic = time.monotonic()
    post_expand_started_at = iso_timestamp_now()
    try:
        post_expand_candidates, _ = request_expand_candidates(
            worker_settings=worker_settings,
            expand_prompt=load_prompt_text(post_expand_prompt_file),
            task_type="post_theorem_expand",
            problem_id=candidate_id,
            stmt=final_statement,
            original_stmt=headline_statement,
            result="proof",
            verify_success=True,
            theory_context=theorem_context,
            open_rows=[normalize_open_problem_row(row) for row in read_jsonl(loop_open_problems_path(data_dir))],
            existing_new_problems=[],
            verify_error_excerpt="",
            current_iteration_full_logs=current_iteration_full_logs,
            same_problem_history_tail=[],
            theory_state=load_theory_state(data_dir),
            max_candidates=MAX_EXPAND_CANDIDATES_PER_PAPER_CLAIM,
        )
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type="paper_claim_session",
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
            session_type="paper_claim_session",
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
        "theorem_name": final_theorem_name,
        "statement": final_statement,
        "docstring_summary": str(selected_candidate.get("docstring_summary", "")).strip(),
        "rationale": "\n".join(part for part in (str(selected_candidate.get("rationale", "")).strip(), last_notes) if part.strip()),
        "supporting_theorems": [theorem for theorem in last_supporting_theorems if theorem in known_theorem_names],
        "intermediate_lemmas": last_helper_theorems,
        "iteration": current_iteration,
        "appended_to_derived": bool(committed_theorem_code),
    }
    with state_lock:
        append_theorem_reuse_memory_entry(loop_theorem_reuse_memory_path(data_dir), theorem_reuse_payload)
        refresh_outcome = store_expand_candidates_and_refresh(
            data_dir=data_dir,
            statements_with_rationale=post_expand_candidates,
            source="post_theorem_expand",
            source_problem_id=final_theorem_name,
            source_kind="paper_claim",
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
    batch_generator_added_problem_rows = list(priority_refresh_report.get("batch_generator_added_problem_rows", []))
    batch_generator_error = str(priority_refresh_report.get("batch_generator_error", ""))
    promoted_expand_rows = list(priority_refresh_report.get("worker_meta", {}).get("promoted_expand_rows", []))
    return {
        "processed": True,
        "candidate_id": candidate_id,
        "status": "proved",
        "verify_success": True,
        "theorem_name": final_theorem_name,
        "statement": final_statement,
        "theorem_code": committed_theorem_code,
        "supporting_theorems": list(last_supporting_theorems),
        "helper_theorems": last_helper_theorems,
        "notes": last_notes,
        "post_theorem_expand_candidates": post_expand_candidates,
        "stored_expand_rows": stored_expand_rows,
        "post_theorem_expand_error": post_expand_error,
        "batch_generator_added_problem_rows": batch_generator_added_problem_rows,
        "batch_generator_error": batch_generator_error,
        "promoted_expand_rows": promoted_expand_rows,
        "priority_refresh_ran": priority_refresh_ran,
        "priority_refresh_error": priority_refresh_error,
        "completed_unit_ids": list(completed_unit_ids),
        "headline_unit_id": headline_unit_id,
        "refuted_unit_ids": [],
        "plan_revisions": plan_revisions,
        "replan_count": total_replan_count,
    }
