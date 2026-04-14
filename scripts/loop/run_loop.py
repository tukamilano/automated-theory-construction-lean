from __future__ import annotations

import argparse
import concurrent.futures
import json
import re
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path
from typing import Callable
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
SCRIPTS_ROOT = SCRIPT_DIR.parent
REPO_ROOT = SCRIPTS_ROOT.parent
scripts_root_str = str(SCRIPTS_ROOT)
if scripts_root_str not in sys.path:
    sys.path.insert(0, scripts_root_str)

from atc_paths import loop_archived_problems_path
from atc_paths import loop_counterexamples_path
from atc_paths import loop_data_dir
from atc_paths import loop_expand_candidates_path
from atc_paths import loop_formalization_memory_path
from atc_paths import loop_open_problems_path
from atc_paths import loop_paper_claim_rejection_memory_path
from atc_paths import loop_solved_problems_path
from atc_paths import loop_theorem_reuse_memory_path
from proof_packets import (
    FormalizerRequestPacket,
    FormalizerResponsePacket,
    ProverRequestPacket,
    ProverResponsePacket,
    RepairRequestPacket,
    SolverStatementRequestPacket,
    normalize_formalizer_payload,
    normalize_prover_payload,
)

from common import (
    ARCHIVED_PROBLEMS_FILENAME,
    LEGACY_DEFERRED_PROBLEMS_FILENAME,
    LEGACY_PRUNED_OPEN_PROBLEMS_FILENAME,
    append_jsonl,
    dedupe_problem_rows_by_stmt,
    load_theory_context,
    merge_archived_problem_rows,
    next_problem_id,
    normalize_open_problem_row,
    normalize_open_problem_priority,
    parse_problem_index,
    partition_open_problem_rows,
    read_archived_problem_rows,
    read_jsonl,
    write_json_atomic,
    write_jsonl_atomic,
)
from derived_entries import extract_derived_theorem_entries
from guidance import unpack_guidance_context
from generated_library import render_scratch_template
from generated_library import scratch_import_modules
from import_inference import infer_minimal_imports, render_import_block
from lean_verify import verify_scratch
from formalization_runtime import attempt_formalization_until_timeout
from loop_common import build_retry_deadline
from loop_common import build_run_artifact_paths
from loop_common import build_run_id
from loop_common import iso_timestamp_now
from loop_common import monotonic_duration_ms
from loop_common import prover_response_fingerprint
from loop_common import remaining_retry_budget_sec
from loop_common import update_same_fingerprint_streak
from loop_helpers import append_derived_entry_cache
from loop_helpers import analyze_lean_statement_compactness
from loop_helpers import append_formalization_memory_entry
from loop_helpers import append_phase_attempt_record
from loop_helpers import build_problem_theory_context
from loop_helpers import emit_phase_log
from loop_helpers import extract_theorem_code_from_scratch
from loop_helpers import is_verified_resolution
from loop_helpers import load_current_guidance
from loop_helpers import load_current_materials
from loop_helpers import load_current_research_agenda
from loop_helpers import load_formalization_memory
from loop_helpers import load_theory_state
from loop_helpers import normalize_stmt_text
from loop_helpers import open_problem_priority_label
from loop_helpers import save_formalization_memory
from loop_helpers import shortlist_relevant_derived_entries
from loop_helpers import statement_within_char_budget
from loop_helpers import validate_theorem_name_stem
from research_agenda import summarize_research_agenda_for_state
from runtime_reset import reset_loop_runtime_data
from runtime_reset import reset_loop_work_files
from state_update import apply_state_update
from theorem_commit import commit_verified_theorem_and_generation
from theorem_reuse_memory import append_theorem_reuse_memory_entry
from worker_client import invoke_worker_json, load_task_worker_settings, load_worker_settings


def debug_log(msg: str) -> None:
    """Print debug message to stderr with timestamp."""
    timestamp = time.strftime("%H:%M:%S")
    print(f"[{timestamp}] {msg}", file=sys.stderr, flush=True)



SCRATCH_TEMPLATE = render_scratch_template()

SCRATCH_OPEN_DECLS = (
    "open Mathling.Lambek.ProductFree\n"
    "open scoped Mathling.Lambek.ProductFree\n\n"
)

DERIVED_TEMPLATE = (
    "import Mathlib\n"
    "import AutomatedTheoryConstruction.Theory\n\n"
    "import AutomatedTheoryConstruction.Generated.Manifest\n\n"
    "set_option autoImplicit false\n\n"
    "namespace AutomatedTheoryConstruction\n\n"
    "open Mathling.Lambek.ProductFree\n"
    "open scoped Mathling.Lambek.ProductFree\n\n"
    "-- Verified theorems are appended here by scripts/append_derived.py.\n"
    "-- Keep any short theorem docstrings/comments here instead of a separate metadata index.\n\n"
    "end AutomatedTheoryConstruction\n"
)
DATA_DIR_PATH = "data"
SEEDS_FILE_PATH = "AutomatedTheoryConstruction/seeds.jsonl"
SCRATCH_FILE_PATH = "AutomatedTheoryConstruction/Scratch.lean"
DERIVED_FILE_PATH = "AutomatedTheoryConstruction/Derived.lean"
THEORY_FILE_PATH = "AutomatedTheoryConstruction/Theory.lean"
FORMALIZATION_MEMORY_FILE_PATH = str(loop_formalization_memory_path(Path(DATA_DIR_PATH)))
ARCHIVED_PROBLEMS_FILE_PATH = str(loop_archived_problems_path(Path(DATA_DIR_PATH)))

RESET_SCRATCH_ON_START = True
RESET_DERIVED_ON_START = True
RESET_FORMALIZATION_MEMORY_ON_START = True

PROVER_STATEMENT_PROMPT_FILE = "prompts/formalize/prover_statement_formalizer.md"
PROVER_PROMPT_FILE = "prompts/prover/prover_simple.md"
FORMALIZER_PROOF_PROMPT_FILE = "prompts/formalize/formalizer_proof.md"
FORMALIZER_COUNTEREXAMPLE_PROMPT_FILE = "prompts/formalize/formalizer_counterexample.md"
REPAIR_PROOF_PROMPT_FILE = "prompts/formalize/repair_proof.md"
REPAIR_COUNTEREXAMPLE_PROMPT_FILE = "prompts/formalize/repair_counterexample.md"
PRIORITIZE_OPEN_PROBLEMS_PROMPT_FILE = "prompts/prioritizer/open_problem_prioritizer.md"
EXPANDER_SOLVED_PROOF_PROMPT_FILE = "prompts/expander/solved_proof.md"

BATCH_GENERATOR_SEED_COUNT = 4
BATCH_GENERATOR_OPEN_TARGET_MIN = 2

THEOREM_NAME_PATTERN = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
UNUSED_VARIABLE_WARNING_PATTERN = re.compile(r"unused variable\s+`([^`]+)`", re.IGNORECASE)
OPEN_PROBLEM_PRIORITY_ORDER = {
    "high": 0,
    "medium": 1,
    "unknown": 2,
    "low": 3,
}

DEFAULT_PROVER_RETRY_BUDGET_SEC = 120
DEFAULT_FORMALIZATION_RETRY_BUDGET_SEC = 300
DEFAULT_MAX_SAME_ERROR_STREAK = 5
COMPILE_METRICS_LOCK = threading.Lock()
LEAN_VERIFY_LOCK = threading.Lock()
DERIVED_UPDATE_LOCK = threading.Lock()

def build_session_scratch_file(base_scratch_file: Path, *, session_type: str, slot_index: int) -> Path:
    stem = base_scratch_file.stem
    suffix = base_scratch_file.suffix or ".lean"
    session_suffix = session_type if slot_index <= 1 else f"{session_type}.{slot_index:03d}"
    return base_scratch_file.with_name(f"{stem}.{session_suffix}{suffix}")


def cleanup_parallel_scratch_files(base_scratch_file: Path) -> None:
    stem = base_scratch_file.stem
    suffix = base_scratch_file.suffix or ".lean"
    for pattern in (
        f"{stem}.loop{suffix}",
        f"{stem}.loop.*{suffix}",
    ):
        for path in base_scratch_file.parent.glob(pattern):
            path.unlink(missing_ok=True)


def append_problem_node_record(
    problem_nodes_path: Path,
    *,
    problem_row: dict[str, Any],
    run_id: str,
    iteration: int,
    session_type: str,
) -> None:
    append_jsonl(
        problem_nodes_path,
        {
            "problem_id": str(problem_row.get("id", "")),
            "stmt": str(problem_row.get("stmt", "")),
            "src": str(problem_row.get("src", "")),
            "priority": open_problem_priority_label(problem_row),
            "created_at_run_id": run_id,
            "created_at_iteration": iteration,
            "created_in_session_type": session_type,
        },
    )


def append_theorem_node_record(
    theorem_nodes_path: Path,
    *,
    theorem_name: str,
    statement: str,
    run_id: str,
    iteration: int,
    session_type: str,
) -> None:
    append_jsonl(
        theorem_nodes_path,
        {
            "theorem_name": theorem_name,
            "statement": statement,
            "created_at_run_id": run_id,
            "created_at_iteration": iteration,
            "created_in_session_type": session_type,
        },
    )


def append_lineage_edge_record(
    lineage_edges_path: Path,
    *,
    run_id: str,
    iteration: int,
    session_type: str,
    parent_id: str,
    child_id: str,
    edge_type: str,
) -> None:
    append_jsonl(
        lineage_edges_path,
        {
            "run_id": run_id,
            "iteration": iteration,
            "session_type": session_type,
            "parent_id": parent_id,
            "child_id": child_id,
            "edge_type": edge_type,
        },
    )


def update_compile_metrics(metrics: dict[str, Any], verify_result: dict[str, Any]) -> None:
    with COMPILE_METRICS_LOCK:
        metrics["compile_attempt_count"] += 1
        if bool(verify_result.get("success", False)):
            metrics["compile_success_count"] += 1


def finalize_run_summary(
    summary_path: Path,
    *,
    run_id: str,
    started_at: str,
    started_monotonic: float,
    metrics: dict[str, Any],
    status: str,
) -> None:
    finished_at = iso_timestamp_now()
    compile_attempt_count = int(metrics.get("compile_attempt_count", 0) or 0)
    compile_success_count = int(metrics.get("compile_success_count", 0) or 0)
    compile_success_rate = (
        compile_success_count / compile_attempt_count
        if compile_attempt_count > 0
        else 0.0
    )
    write_json_atomic(
        summary_path,
        {
            "run_id": run_id,
            "started_at": started_at,
            "finished_at": finished_at,
            "duration_ms": monotonic_duration_ms(started_monotonic),
            "status": status,
            "success": bool(metrics.get("solved_per_run", 0) >= 1),
            "solved_per_run": int(metrics.get("solved_per_run", 0) or 0),
            "compile_attempt_count": compile_attempt_count,
            "compile_success_count": compile_success_count,
            "compile_success_rate": compile_success_rate,
            "time_to_first_green_ms": metrics.get("time_to_first_green_ms"),
            "wall_clock_to_last_solve_ms": metrics.get("wall_clock_to_last_solve_ms"),
        },
    )


def theory_state_path(data_dir: Path) -> Path:
    return loop_data_dir(data_dir) / "theory_state.json"


def write_theory_state(
    data_dir: Path,
    *,
    run_id: str,
    current_iteration: int,
    derived_theorem_count: int,
    open_problem_count: int,
    archived_problem_count: int,
    theory_snapshot: str,
    next_direction: dict[str, Any],
    important_verified_counterexamples: list[str],
    research_agenda_summary: dict[str, Any] | None = None,
    theory_frontier: dict[str, list[str]] | None = None,
) -> dict[str, Any]:
    existing_payload = load_theory_state(data_dir)
    frontier = dict(theory_frontier or {})
    payload = {
        "version": 1,
        "updated_at_iteration": current_iteration,
        "updated_at_run_id": run_id,
        "theory_snapshot": theory_snapshot,
        "next_direction": next_direction,
        "important_verified_counterexamples": list(important_verified_counterexamples),
        "research_agenda": dict(research_agenda_summary or {}),
        "summary_basis": {
            "derived_theorem_count": derived_theorem_count,
            "open_problem_count": open_problem_count,
            "archived_problem_count": archived_problem_count,
        },
        "desired_summary_changes": list(frontier.get("desired_summary_changes", [])),
        "current_bottlenecks": list(frontier.get("current_bottlenecks", [])),
        "overexplored_patterns": list(frontier.get("overexplored_patterns", [])),
        "missing_bridges": list(frontier.get("missing_bridges", [])),
        "agenda_pressure": list(frontier.get("agenda_pressure", [])),
    }
    if "derived_generation" in existing_payload:
        payload["derived_generation"] = int(existing_payload.get("derived_generation", 0) or 0)
    write_json_atomic(theory_state_path(data_dir), payload)
    return payload


def append_theory_state_history(
    history_path: Path,
    *,
    run_id: str,
    current_iteration: int,
    theory_state: dict[str, Any],
) -> None:
    append_jsonl(
        history_path,
        {
            "run_id": run_id,
            "updated_at_iteration": current_iteration,
            "theory_state": theory_state,
        },
    )


def load_derived_generation(data_dir: Path) -> int:
    theory_state = load_theory_state(data_dir)
    return int(theory_state.get("derived_generation", 0) or 0)


def persist_derived_generation(
    data_dir: Path,
    *,
    generation: int,
    run_id: str,
    current_iteration: int,
) -> dict[str, Any]:
    payload = load_theory_state(data_dir)
    if not payload:
        payload = {
            "version": 1,
            "updated_at_iteration": current_iteration,
            "updated_at_run_id": run_id,
            "theory_snapshot": "",
            "next_direction": {},
            "important_verified_counterexamples": [],
            "research_agenda": {},
            "desired_summary_changes": [],
            "current_bottlenecks": [],
            "overexplored_patterns": [],
            "missing_bridges": [],
            "agenda_pressure": [],
            "summary_basis": {
                "derived_theorem_count": 0,
                "open_problem_count": 0,
                "archived_problem_count": 0,
            },
        }
    payload["derived_generation"] = int(generation)
    payload["updated_at_iteration"] = current_iteration
    payload["updated_at_run_id"] = run_id
    write_json_atomic(theory_state_path(data_dir), payload)
    return payload

MAX_EXPAND_CANDIDATES_PER_SOLVED_PROOF = 3



def append_expand_candidates(
    *,
    data_dir: Path,
    statements_with_rationale: list[dict[str, str]],
    source: str,
    source_problem_id: str,
    source_kind: str,
) -> list[dict[str, Any]]:
    if not statements_with_rationale:
        return []

    open_rows = [normalize_open_problem_row(row) for row in read_jsonl(loop_open_problems_path(data_dir))]
    archived_rows = read_archived_problem_rows(data_dir)
    solved_rows = read_jsonl(loop_solved_problems_path(data_dir))
    counter_rows = read_jsonl(loop_counterexamples_path(data_dir))

    seen_norms = {
        normalize_stmt_text(str(row.get("stmt", "")))
        for row in (open_rows + archived_rows + solved_rows + counter_rows)
        if str(row.get("stmt", "")).strip()
    }
    all_ids = [
        str(row.get("id", ""))
        for row in (open_rows + archived_rows + solved_rows + counter_rows)
    ]

    added_rows: list[dict[str, Any]] = []
    next_rows = list(open_rows)
    for item in statements_with_rationale:
        stmt = str(item.get("statement", "")).strip()
        rationale = str(item.get("rationale", "")).strip()
        norm = normalize_stmt_text(stmt)
        if not stmt or not norm or norm in seen_norms:
            continue
        new_id = next_problem_id(all_ids)
        all_ids.append(new_id)
        seen_norms.add(norm)
        new_row = normalize_open_problem_row(
            {
                "id": new_id,
                "stmt": stmt,
                "src": source,
                "mode": "expand_candidate",
                "summary_delta": rationale,
                "source_kind": "expand_candidate",
                "generated_from_source_id": source_problem_id,
                "generated_from_source_kind": source_kind,
                "priority": "unknown",
                "priority_rationale": "",
                "failure_count": 0,
            }
        )
        next_rows.append(new_row)
        added_rows.append(dict(new_row))

    if added_rows:
        write_jsonl_atomic(loop_open_problems_path(data_dir), dedupe_problem_rows_by_stmt(next_rows))
    return added_rows


def collect_important_verified_counterexamples(
    data_dir: Path,
    *,
    max_items: int = 3,
    max_chars: int = 240,
) -> list[str]:
    rows = read_jsonl(loop_counterexamples_path(data_dir))
    summaries: list[str] = []
    seen_stmt_norms: set[str] = set()
    for row in reversed(rows):
        stmt = normalize_stmt_text(str(row.get("stmt", "")))
        if not stmt or stmt in seen_stmt_norms:
            continue
        seen_stmt_norms.add(stmt)
        summary = stmt
        if len(summary) > max_chars:
            summary = summary[: max_chars - 3] + "..."
        summaries.append(summary)
        if len(summaries) >= max_items:
            break
    return summaries


def is_solver_eligible_open_problem(row: dict[str, Any]) -> bool:
    return open_problem_priority_label(row) in {"high", "medium"}


def has_available_solver_eligible_problem(
    open_rows: list[dict[str, Any]],
    *,
    reserved_problem_ids: set[str],
) -> bool:
    for row in open_rows:
        problem_id = str(row.get("id", "")).strip()
        if not problem_id or problem_id in reserved_problem_ids:
            continue
        if is_solver_eligible_open_problem(row):
            return True
    return False


def open_problem_sort_key(
    row: dict[str, Any],
    *,
    failure_archive_threshold: int,
) -> tuple[int, int, int]:
    priority_order = OPEN_PROBLEM_PRIORITY_ORDER.get(open_problem_priority_label(row), OPEN_PROBLEM_PRIORITY_ORDER["unknown"])
    failure_count = int(row.get("failure_count", 0) or 0)
    archived = 1 if failure_archive_threshold > 0 and failure_count >= failure_archive_threshold else 0
    return (archived, priority_order, failure_count)


def sort_open_problem_queue(
    open_rows: list[dict[str, Any]],
    *,
    failure_archive_threshold: int,
) -> list[dict[str, Any]]:
    normalized_rows = [normalize_open_problem_row(row) for row in open_rows]
    return sorted(
        normalized_rows,
        key=lambda row: open_problem_sort_key(row, failure_archive_threshold=failure_archive_threshold),
    )


def split_active_and_archived_problem_queues(
    tracked_rows: list[dict[str, Any]],
    *,
    failure_archive_threshold: int,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    sorted_rows = sort_open_problem_queue(
        tracked_rows,
        failure_archive_threshold=failure_archive_threshold,
    )
    return partition_open_problem_rows(
        sorted_rows,
        failure_threshold=failure_archive_threshold,
    )


def apply_open_problem_priorities(
    open_rows: list[dict[str, Any]],
    priority_updates: list[dict[str, str]],
) -> list[dict[str, Any]]:
    updates_by_id = {item["problem_id"]: item for item in priority_updates}
    updated_rows: list[dict[str, Any]] = []
    for row in open_rows:
        normalized = normalize_open_problem_row(row)
        update = updates_by_id.get(str(normalized.get("id", "")))
        if update is not None:
            normalized["priority"] = update["priority"]
            normalized["priority_rationale"] = update["rationale"]
        updated_rows.append(normalized)
    return updated_rows


def needs_bootstrap_priority_refresh(open_rows: list[dict[str, Any]]) -> bool:
    return any(open_problem_priority_label(row) == "unknown" for row in open_rows)


def should_generate_expand_candidates(*, verify_success: bool, result: str) -> bool:
    return is_verified_resolution(verify_success=verify_success, result=result)


def normalize_docstring_summary(text: str, max_chars: int = 240) -> str:
    cleaned = " ".join(str(text).replace("```", " ").split())
    if not cleaned:
        return ""
    if len(cleaned) <= max_chars:
        return cleaned
    return cleaned[: max_chars - 3] + "..."


def build_theorem_docstring(
    *,
    problem_id: str,
    docstring_summary: str,
    theorem_name_stem: str,
    statement_formalization_notes: str,
) -> str:
    summary = normalize_docstring_summary(docstring_summary)
    if not summary:
        summary = normalize_docstring_summary(theorem_name_stem.replace("_", " "))
    if not summary:
        summary = normalize_docstring_summary(statement_formalization_notes)
    if not summary:
        return "Auto-generated theorem."
    if summary[-1] not in ".!?":
        summary += "."
    return summary


def pick_next_problem(open_rows: list[dict[str, Any]]) -> dict[str, Any] | None:
    return open_rows[0] if open_rows else None


def pick_next_available_problem(
    open_rows: list[dict[str, Any]],
    *,
    reserved_problem_ids: set[str],
) -> dict[str, Any] | None:
    for row in open_rows:
        problem_id = str(row.get("id", "")).strip()
        if not problem_id or problem_id in reserved_problem_ids:
            continue
        if not is_solver_eligible_open_problem(row):
            continue
        return row
    return None


def validate_prover_output(
    payload: dict[str, Any],
    expected_problem_id: str,
) -> ProverResponsePacket:
    required_keys = {"problem_id", "result", "proof_sketch", "counterexample_text"}
    missing_keys = sorted(required_keys - set(payload.keys()))
    if missing_keys:
        raise ValueError(f"prover output missing required keys: {', '.join(missing_keys)}")

    problem_id = payload.get("problem_id")
    if problem_id != expected_problem_id:
        raise ValueError("prover output problem_id does not match picked problem")

    result = payload.get("result")
    if result not in {"proof", "counterexample", "stuck"}:
        raise ValueError("prover result must be one of: proof, counterexample, stuck")

    proof_sketch = payload.get("proof_sketch")
    counterexample_text = payload.get("counterexample_text")
    if not isinstance(proof_sketch, str) or not isinstance(counterexample_text, str):
        raise ValueError("proof_sketch and counterexample_text must be strings")
    new_problems = payload.get("new_problems", [])
    if not isinstance(new_problems, list) or any(not isinstance(item, str) for item in new_problems):
        raise ValueError("new_problems must be a list of strings")

    return ProverResponsePacket(
        problem_id=problem_id,
        result=result,
        proof_sketch=proof_sketch,
        counterexample_text=counterexample_text,
        new_problems=[
            item.strip()
            for item in new_problems
            if item.strip() and statement_within_char_budget(item.strip())
        ][:2],
        raw_payload=dict(payload),
    )


def validate_theorem_name(theorem_name: str) -> str:
    cleaned = theorem_name.strip()
    if not cleaned:
        raise ValueError("theorem_name must be non-empty")
    if cleaned == "None":
        raise ValueError("theorem_name must not be the literal None")
    if not THEOREM_NAME_PATTERN.fullmatch(cleaned):
        raise ValueError("theorem_name must match ^[A-Za-z_][A-Za-z0-9_']*$")
    return cleaned


def build_theorem_name(problem_id: str, theorem_name_stem: str) -> str:
    problem_index = parse_problem_index(problem_id)
    if problem_index is None:
        raise ValueError(f"invalid problem_id for theorem naming: {problem_id}")
    stem = validate_theorem_name_stem(theorem_name_stem)
    return f"thm_{stem}_{problem_index:06d}"


def validate_prover_statement_output(payload: dict[str, Any], expected_problem_id: str) -> tuple[str, str, str, str, str, str]:
    allowed_key_sets = [
        {"problem_id", "result", "lean_statement", "theorem_name_stem", "docstring_summary", "notes"},
        {
            "problem_id",
            "result",
            "statement_prelude_code",
            "lean_statement",
            "theorem_name_stem",
            "docstring_summary",
            "notes",
        },
    ]
    if set(payload.keys()) not in allowed_key_sets:
        raise ValueError(
            "prover_statement output must contain exactly: problem_id, result, lean_statement, theorem_name_stem, "
            "docstring_summary, notes with optional statement_prelude_code"
        )

    problem_id = payload.get("problem_id")
    if problem_id != expected_problem_id:
        raise ValueError("prover_statement output problem_id does not match picked problem")

    result = payload.get("result")
    if result not in {"ok", "stuck"}:
        raise ValueError("prover_statement result must be one of: ok, stuck")

    statement_prelude_code = payload.get("statement_prelude_code", "")
    lean_statement = payload.get("lean_statement")
    theorem_name_stem = payload.get("theorem_name_stem")
    docstring_summary = payload.get("docstring_summary")
    notes = payload.get("notes")
    if (
        not isinstance(statement_prelude_code, str)
        or not isinstance(lean_statement, str)
        or not isinstance(theorem_name_stem, str)
        or not isinstance(docstring_summary, str)
        or not isinstance(notes, str)
    ):
        raise ValueError(
            "prover_statement statement_prelude_code, lean_statement, theorem_name_stem, docstring_summary, and notes must be strings"
        )
    if result == "ok" and not lean_statement.strip():
        raise ValueError("prover_statement lean_statement must be non-empty when result=ok")
    if result == "ok":
        theorem_name_stem = validate_theorem_name_stem(theorem_name_stem)
    else:
        statement_prelude_code = statement_prelude_code.strip()
        if statement_prelude_code:
            raise ValueError("prover_statement statement_prelude_code must be empty when result=stuck")
        theorem_name_stem = theorem_name_stem.strip()
        if theorem_name_stem:
            raise ValueError("prover_statement theorem_name_stem must be empty when result=stuck")
        docstring_summary = docstring_summary.strip()
        if docstring_summary:
            raise ValueError("prover_statement docstring_summary must be empty when result=stuck")

    return (
        result,
        statement_prelude_code.strip(),
        lean_statement.strip(),
        theorem_name_stem,
        docstring_summary.strip(),
        notes.strip(),
    )


def validate_formalizer_output(
    payload: dict[str, Any],
    expected_problem_id: str,
) -> FormalizerResponsePacket:
    allowed_key_sets = [
        {"problem_id", "result", "proof_sketch", "proof_text", "counterexample_text"},
        {"problem_id", "result", "proof_sketch", "prelude_code", "proof_text", "counterexample_text"},
    ]
    if set(payload.keys()) not in allowed_key_sets:
        raise ValueError(
            "formalizer output must contain exactly: problem_id, result, proof_sketch, proof_text, counterexample_text"
            " with optional prelude_code"
        )

    problem_id = payload.get("problem_id")
    if problem_id != expected_problem_id:
        raise ValueError("formalizer output problem_id does not match picked problem")

    result = payload.get("result")
    if result not in {"proof", "counterexample", "stuck"}:
        raise ValueError("formalizer result must be one of: proof, counterexample, stuck")

    proof_sketch = payload.get("proof_sketch")
    prelude_code = payload.get("prelude_code", "")
    proof_text = payload.get("proof_text")
    counterexample_text = payload.get("counterexample_text")
    if (
        not isinstance(proof_sketch, str)
        or not isinstance(prelude_code, str)
        or not isinstance(proof_text, str)
        or not isinstance(counterexample_text, str)
    ):
        raise ValueError("formalizer proof_sketch, prelude_code, proof_text and counterexample_text must be strings")

    return normalize_formalizer_payload(
        {
            "problem_id": problem_id,
            "result": result,
            "proof_sketch": proof_sketch,
            "prelude_code": prelude_code,
            "proof_text": proof_text,
            "counterexample_text": counterexample_text,
        },
        expected_problem_id,
    )


def validate_problem_candidates_output(
    payload: dict[str, Any],
    *,
    expected_problem_id: str,
    max_candidates: int,
) -> list[dict[str, str]]:
    required_keys = {"problem_id", "candidates"}
    if set(payload.keys()) != required_keys:
        raise ValueError("candidate output must contain exactly: problem_id, candidates")

    problem_id = str(payload.get("problem_id", "")).strip()
    if problem_id != expected_problem_id:
        raise ValueError("candidate output problem_id does not match request")

    candidates_value = payload.get("candidates")
    if not isinstance(candidates_value, list):
        raise ValueError("candidate output candidates must be an array of objects")
    if len(candidates_value) > max_candidates:
        raise ValueError(f"candidate output candidates must have length <= {max_candidates}")

    parsed: list[dict[str, str]] = []
    seen_norms: set[str] = set()
    for item in candidates_value:
        if not isinstance(item, dict) or set(item.keys()) != {"statement", "rationale"}:
            raise ValueError("each candidate must contain exactly: statement, rationale")
        statement = item.get("statement")
        rationale = item.get("rationale")
        if not isinstance(statement, str) or not isinstance(rationale, str):
            raise ValueError("candidate statement and rationale must be strings")
        normalized_statement = statement.strip()
        if not normalized_statement:
            continue
        if not statement_within_char_budget(normalized_statement):
            continue
        norm = normalize_stmt_text(normalized_statement)
        if norm in seen_norms:
            continue
        seen_norms.add(norm)
        parsed.append({"statement": normalized_statement, "rationale": rationale.strip()})

    return parsed[:max_candidates]


def validate_next_direction_payload(payload: Any) -> dict[str, str]:
    required_keys = {"label", "guidance", "rationale"}
    if not isinstance(payload, dict) or set(payload.keys()) != required_keys:
        raise ValueError("next_direction must contain exactly: label, guidance, rationale")

    label = str(payload.get("label", "")).strip()
    guidance = str(payload.get("guidance", "")).strip()
    rationale = str(payload.get("rationale", "")).strip()
    if not label or not guidance or not rationale:
        raise ValueError("next_direction label, guidance, and rationale must be non-empty")
    return {
        "label": label,
        "guidance": guidance,
        "rationale": rationale,
    }


def validate_theory_snapshot_payload(payload: Any) -> str:
    theory_snapshot = str(payload or "").strip()
    if not theory_snapshot:
        raise ValueError("theory_snapshot must be non-empty")
    return theory_snapshot


def validate_string_list_payload(payload: Any, field_name: str, *, max_items: int = 6) -> list[str]:
    if not isinstance(payload, list):
        raise ValueError(f"{field_name} must be an array of strings")

    parsed: list[str] = []
    seen_norms: set[str] = set()
    for item in payload:
        if not isinstance(item, str):
            raise ValueError(f"{field_name} must contain only strings")
        value = item.strip()
        if not value:
            continue
        norm = " ".join(value.split()).lower()
        if norm in seen_norms:
            continue
        seen_norms.add(norm)
        parsed.append(value)
    return parsed[:max_items]


def validate_open_problem_priority_output(
    payload: dict[str, Any],
    expected_problem_ids: list[str],
) -> tuple[list[dict[str, str]], str, dict[str, str], dict[str, list[str]]]:
    required_keys = {
        "priorities",
        "theory_snapshot",
        "next_direction",
        "desired_summary_changes",
        "current_bottlenecks",
        "overexplored_patterns",
        "missing_bridges",
        "agenda_pressure",
    }
    if set(payload.keys()) != required_keys:
        raise ValueError(
            "priority refresh output must contain exactly: priorities, theory_snapshot, next_direction, desired_summary_changes, current_bottlenecks, overexplored_patterns, missing_bridges, agenda_pressure"
        )

    priorities_value = payload.get("priorities")
    if not isinstance(priorities_value, list):
        raise ValueError("priority refresh priorities must be an array of objects")

    expected_id_set = set(expected_problem_ids)
    seen_ids: set[str] = set()
    parsed: list[dict[str, str]] = []

    for item in priorities_value:
        if not isinstance(item, dict) or set(item.keys()) != {"problem_id", "priority", "rationale"}:
            raise ValueError("each priority item must contain exactly: problem_id, priority, rationale")
        problem_id = str(item.get("problem_id", "")).strip()
        priority = normalize_open_problem_priority(item.get("priority"))
        rationale = str(item.get("rationale", "")).strip()
        if problem_id not in expected_id_set:
            raise ValueError(f"unexpected problem_id in priority refresh output: {problem_id}")
        if problem_id in seen_ids:
            raise ValueError(f"duplicate problem_id in priority refresh output: {problem_id}")
        if priority not in {"high", "medium", "low"}:
            raise ValueError(f"priority must be high|medium|low, got {priority}")
        seen_ids.add(problem_id)
        parsed.append(
            {
                "problem_id": problem_id,
                "priority": priority,
                "rationale": rationale,
            }
        )

    if seen_ids != expected_id_set:
        missing = sorted(expected_id_set - seen_ids)
        raise ValueError(f"priority refresh output missing problem_ids: {missing}")

    theory_frontier = {
        "desired_summary_changes": validate_string_list_payload(
            payload.get("desired_summary_changes"),
            "desired_summary_changes",
        ),
        "current_bottlenecks": validate_string_list_payload(
            payload.get("current_bottlenecks"),
            "current_bottlenecks",
        ),
        "overexplored_patterns": validate_string_list_payload(
            payload.get("overexplored_patterns"),
            "overexplored_patterns",
        ),
        "missing_bridges": validate_string_list_payload(
            payload.get("missing_bridges"),
            "missing_bridges",
        ),
        "agenda_pressure": validate_string_list_payload(
            payload.get("agenda_pressure"),
            "agenda_pressure",
        ),
    }

    return (
        parsed,
        validate_theory_snapshot_payload(payload.get("theory_snapshot")),
        validate_next_direction_payload(payload.get("next_direction")),
        theory_frontier,
    )


def load_prompt_text(prompt_file: str) -> str:
    path = Path(prompt_file)
    from prompt_loader import load_prompt_file

    return load_prompt_file(path)


def select_formalizer_prompt(prompt_map: dict[str, str], *, result: str) -> str:
    if result == "counterexample":
        return prompt_map["counterexample"]
    return prompt_map["proof"]


def formalize_to_scratch(
    theorem_name: str,
    stmt: str,
    mode: str,
    proof_text: str,
    counterexample_text: str,
    prelude_code: str = "",
) -> tuple[str, str]:
    theorem_name = validate_theorem_name(theorem_name)
    _ = stmt
    extra_imports = infer_minimal_imports("")
    if mode == "proof":
        raw_body = proof_text.strip() if proof_text.strip() else "sorry"
        body = "\n  ".join(line.rstrip() for line in raw_body.splitlines())
        theorem = f"theorem {theorem_name} : {stmt} := by\n  {body}\n"
    else:  # mode == "counterexample"
        # For counterexample: proof_text contains the proof that the negation holds.
        # We prove ¬(stmt), which is logically equivalent to disproving the original statement.
        # The proof_text should construct a counterexample and derive a contradiction from stmt.
        raw_body = proof_text.strip() if proof_text.strip() else "sorry"
        body = "\n  ".join(line.rstrip() for line in raw_body.splitlines())
        theorem = f"theorem {theorem_name}_is_false : ¬({stmt}) := by\n  {body}\n"

    prelude_block = prelude_code.strip()
    if prelude_block:
        prelude_block = prelude_block + "\n\n"

    scratch = (
        render_import_block(extra_imports)
        + "\n".join(f"import {module_name}" for module_name in scratch_import_modules())
        + "\n\n"
        "set_option autoImplicit false\n\n"
        "namespace AutomatedTheoryConstruction\n\n"
        f"{SCRATCH_OPEN_DECLS}"
        f"{prelude_block}"
        f"{theorem}\n"
        "end AutomatedTheoryConstruction\n"
    )
    return theorem_name, scratch


def write_formalization_candidate_to_scratch(
    *,
    scratch_file: Path,
    theorem_name: str,
    stmt: str,
    result: str,
    prelude_code: str,
    proof_text: str,
    counterexample_text: str,
) -> None:
    _, scratch = formalize_to_scratch(
        theorem_name=theorem_name,
        stmt=stmt,
        mode=result,
        proof_text=proof_text,
        counterexample_text=counterexample_text,
        prelude_code=prelude_code,
    )
    scratch_file.parent.mkdir(parents=True, exist_ok=True)
    scratch_file.write_text(scratch, encoding="utf-8")


def validate_solver_statement_with_lean(
    *,
    problem_id: str,
    theorem_name: str,
    stmt: str,
    statement_prelude_code: str = "",
    timeout_sec: int = 180,
) -> dict[str, Any]:
    _, scratch = formalize_to_scratch(
        theorem_name=theorem_name,
        stmt=stmt,
        mode="proof",
        prelude_code=statement_prelude_code,
        proof_text="sorry",
        counterexample_text="",
    )
    temp_path: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            suffix=".lean",
            prefix=f"stmt_check_{problem_id}_",
            delete=False,
        ) as handle:
            handle.write(scratch)
            temp_path = Path(handle.name)
        with LEAN_VERIFY_LOCK:
            return verify_scratch(problem_id, "proof", temp_path, timeout_sec=timeout_sec)
    finally:
        if temp_path is not None:
            temp_path.unlink(missing_ok=True)


def append_current_iteration_log(
    current_iteration_full_logs: list[dict[str, Any]],
    *,
    stage: str,
    index: int,
    worker_meta: dict[str, Any],
) -> None:
    raw_model_output = worker_meta.get("raw_model_output")
    if not isinstance(raw_model_output, str) or not raw_model_output.strip():
        return
    current_iteration_full_logs.append(
        {
            "stage": stage,
            "index": index,
            "raw_model_output": raw_model_output,
        }
    )


def emit_parse_phase_log(
    enabled: bool,
    phase: str,
    *,
    iteration: int,
    problem_id: str,
    worker_meta: dict[str, Any],
    repair_round: int | None = None,
) -> None:
    worker_attempts = int(worker_meta.get("json_parse_attempts", 0) or 0)
    client_attempts = int(worker_meta.get("client_json_parse_attempts", 0) or 0)
    worker_fallback = bool(worker_meta.get("raw_parse_fallback_used", False))
    client_fallback = bool(worker_meta.get("client_raw_parse_fallback_used", False))

    # Default successful parses are noisy and low-signal; only emit when recovery/fallback happened.
    if worker_attempts <= 1 and client_attempts <= 1 and not worker_fallback and not client_fallback:
        return

    payload: dict[str, Any] = {
        "iteration": iteration,
        "problem_id": problem_id,
        "worker_attempts": worker_attempts,
        "client_attempts": client_attempts,
    }
    if repair_round is not None:
        payload["repair_round"] = repair_round
    if worker_fallback or client_fallback:
        payload["fallback_used"] = worker_fallback or client_fallback
    emit_phase_log(enabled, phase, **payload)


def is_worker_timeout_error(exc: Exception) -> bool:
    message = str(exc).lower()
    if "keyboardinterrupt" in message or "exited with code 130" in message or "interrupt_requested" in message:
        return False
    return "timed out" in message or "timeout" in message


def store_expand_candidates_and_refresh(
    *,
    data_dir: Path,
    statements_with_rationale: list[dict[str, str]],
    source: str,
    source_problem_id: str,
    source_kind: str,
    prioritize_worker_settings: Any,
    prioritizer_prompt_file: str,
    derived_entries: list[dict[str, str]],
    current_iteration: int,
    failure_threshold: int,
    run_id: str,
    theory_state_history_path: Path | None,
    theory_file: Path,
    derived_file: Path,
    repo_root: Path,
    batch_generator_seed_count: int,
    batch_generator_open_target_min: int,
    allow_backfill: bool = True,
    phase_logger: Callable[..., None] | None = None,
) -> dict[str, Any]:
    stored_expand_rows = append_expand_candidates(
        data_dir=data_dir,
        statements_with_rationale=statements_with_rationale,
        source=source,
        source_problem_id=source_problem_id,
        source_kind=source_kind,
    )

    refresh_result = refresh_open_problem_state(
        data_dir=data_dir,
        prioritize_worker_settings=prioritize_worker_settings,
        prioritizer_prompt_file=prioritizer_prompt_file,
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
        allow_backfill=allow_backfill,
        phase_logger=phase_logger,
    )
    refresh_result["stored_expand_rows"] = stored_expand_rows
    return refresh_result


def refresh_open_problem_state(
    *,
    data_dir: Path,
    prioritize_worker_settings: Any,
    prioritizer_prompt_file: str,
    derived_entries: list[dict[str, str]],
    current_iteration: int,
    failure_threshold: int,
    run_id: str,
    theory_state_history_path: Path | None,
    theory_file: Path,
    derived_file: Path,
    repo_root: Path,
    batch_generator_seed_count: int,
    batch_generator_open_target_min: int,
    reserved_problem_ids: set[str] | None = None,
    allow_backfill: bool = True,
    phase_logger: Callable[..., None] | None = None,
) -> dict[str, Any]:
    if allow_backfill:
        backfill_ran, backfill_error, backfill_report = backfill_open_problems_if_needed(
            data_dir=data_dir,
            theory_file=theory_file,
            derived_file=derived_file,
            repo_root=repo_root,
            batch_generator_seed_count=batch_generator_seed_count,
            batch_generator_open_target_min=batch_generator_open_target_min,
            reserved_problem_ids=reserved_problem_ids,
            phase_logger=phase_logger,
        )
    else:
        backfill_ran, backfill_error, backfill_report = False, "", {
            "batch_generator_added_problem_rows": [],
            "batch_generator_error": "",
        }
    priority_refresh_ran, priority_refresh_error, priority_refresh_worker_meta = force_refresh_open_problem_priorities(
        data_dir=data_dir,
        worker_settings=prioritize_worker_settings,
        prioritizer_prompt_file=prioritizer_prompt_file,
        derived_entries=derived_entries,
        current_iteration=current_iteration,
        failure_threshold=failure_threshold,
        run_id=run_id,
        theory_state_history_path=theory_state_history_path,
    )
    return {
        "priority_refresh_ran": bool(priority_refresh_ran or backfill_ran),
        "priority_refresh_error": str(backfill_error or priority_refresh_error or ""),
        "priority_refresh_failed": bool(not priority_refresh_ran and bool(priority_refresh_error)),
        "priority_refresh_report": {
            "worker_meta": priority_refresh_worker_meta,
            "batch_generator_added_problem_rows": list(backfill_report.get("batch_generator_added_problem_rows", [])),
            "batch_generator_error": str(backfill_report.get("batch_generator_error", "") or backfill_error or ""),
        },
    }


def analyze_lean_failure(
    stderr: str,
    stdout: str,
    *,
    verify_result: dict[str, Any] | None = None,
) -> dict[str, Any]:
    error = verify_result or {}
    if verify_result is not None:
        text = ""
        direct_categories = []
        cat_value = error.get("error_category")
        if isinstance(cat_value, str):
            direct_categories.extend([item.strip() for item in cat_value.split(",") if item.strip()])
        elif isinstance(cat_value, list):
            direct_categories.extend([str(item).strip() for item in cat_value if str(item).strip()])

        diagnostics = error.get("diagnostics")
        if diagnostics is None:
            diagnostics = (stderr or "") + "\n" + (stdout or "")
        elif isinstance(diagnostics, list):
            diagnostics = "\n".join(str(item).strip() for item in diagnostics if str(item).strip())
        else:
            diagnostics = str(diagnostics)
        text = diagnostics
    else:
        direct_categories = []
        text = (stderr or "") + "\n" + (stdout or "")

    lines = [line.strip() for line in text.splitlines() if line.strip()]
    top_lines = lines[:12]
    categories: list[str] = []

    for category in direct_categories:
        if category and category not in categories:
            categories.append(category)

    if "Type mismatch" in text:
        categories.append("type_mismatch")
    if "rewrite` failed" in text or "Tactic `rewrite` failed" in text:
        categories.append("rewrite_failed")
    if "unsolved goals" in text:
        categories.append("unsolved_goals")
    if "unknown constant" in text or "unknown identifier" in text:
        categories.append("unknown_symbol")
    if "unknown tactic" in text:
        categories.append("unknown_tactic")
    if "Application type mismatch" in text:
        categories.append("application_type_mismatch")
    normalized_categories: list[str] = []
    for item in categories:
        if item and item not in normalized_categories:
            normalized_categories.append(item)
    categories = normalized_categories

    if not categories:
        categories.append("other")

    fingerprint_source = [line for line in top_lines if line]
    if not fingerprint_source:
        fingerprint_source = ["no_diagnostics"]
    if error.get("executor_metadata"):
        metadata = error.get("executor_metadata")
        if isinstance(metadata, dict):
            toolchain = str(metadata.get("toolchain", "")).strip()
            if toolchain:
                fingerprint_source.append(f"toolchain={toolchain}")

    fingerprint = " | ".join(fingerprint_source[:3]) if fingerprint_source else "no_diagnostics"
    return {
        "fingerprint": fingerprint,
        "categories": categories,
        "top_lines": top_lines,
    }


def text_contains_sorry(text: str) -> bool:
    return bool(re.search(r"\bsorry\b", text))


def file_contains_sorry(path: Path) -> bool:
    try:
        content = path.read_text(encoding="utf-8")
    except Exception:
        return False
    return text_contains_sorry(content)


def extract_unused_variable_names(stderr: str, stdout: str) -> list[str]:
    text = (stderr or "") + "\n" + (stdout or "")
    names: list[str] = []
    seen: set[str] = set()
    for match in UNUSED_VARIABLE_WARNING_PATTERN.finditer(text):
        name = str(match.group(1)).strip()
        if not name or name in seen:
            continue
        seen.add(name)
        names.append(name)
    return names


def _find_matching_delimiter(text: str, start: int) -> int:
    pairs = {"(": ")", "{": "}", "[": "]"}
    closing_to_opening = {value: key for key, value in pairs.items()}
    opening = text[start]
    if opening not in pairs:
        return -1
    stack = [opening]
    idx = start + 1
    while idx < len(text):
        ch = text[idx]
        if ch in pairs:
            stack.append(ch)
        elif ch in closing_to_opening:
            if not stack or stack[-1] != closing_to_opening[ch]:
                return -1
            stack.pop()
            if not stack:
                return idx
        idx += 1
    return -1


def _find_top_level_colon(text: str) -> int:
    depth_paren = 0
    depth_brace = 0
    depth_bracket = 0
    for idx, ch in enumerate(text):
        if ch == "(":
            depth_paren += 1
        elif ch == ")":
            depth_paren = max(0, depth_paren - 1)
        elif ch == "{":
            depth_brace += 1
        elif ch == "}":
            depth_brace = max(0, depth_brace - 1)
        elif ch == "[":
            depth_bracket += 1
        elif ch == "]":
            depth_bracket = max(0, depth_bracket - 1)
        elif ch == ":" and depth_paren == 0 and depth_brace == 0 and depth_bracket == 0:
            return idx
    return -1


def prune_unused_binders_from_statement(stmt: str, unused_names: list[str]) -> str:
    if not unused_names:
        return stmt

    stripped = stmt.lstrip()
    if not stripped.startswith("∀"):
        return stmt

    idx = 1
    binders: list[str] = []
    while idx < len(stripped):
        while idx < len(stripped) and stripped[idx].isspace():
            idx += 1
        if idx >= len(stripped):
            return stmt
        if stripped[idx] == ",":
            body = stripped[idx + 1 :].strip()
            break
        if stripped[idx] not in "({[":
            return stmt
        end_idx = _find_matching_delimiter(stripped, idx)
        if end_idx < 0:
            return stmt
        binders.append(stripped[idx : end_idx + 1])
        idx = end_idx + 1
    else:
        return stmt

    unused_set = set(unused_names)
    kept_binders: list[str] = []
    changed = False

    for binder in binders:
        opener = binder[0]
        closer = binder[-1]
        if opener == "[":
            kept_binders.append(binder)
            continue
        inner = binder[1:-1].strip()
        colon_idx = _find_top_level_colon(inner)
        if colon_idx < 0:
            kept_binders.append(binder)
            continue
        names_part = inner[:colon_idx].strip()
        type_part = inner[colon_idx + 1 :].strip()
        names = [token for token in names_part.split() if token]
        if not names:
            kept_binders.append(binder)
            continue
        kept_names = [name for name in names if name not in unused_set]
        if len(kept_names) == len(names):
            kept_binders.append(binder)
            continue
        changed = True
        if kept_names:
            kept_binders.append(f"{opener}{' '.join(kept_names)} : {type_part}{closer}")

    if not changed:
        return stmt
    if not kept_binders:
        return body
    return f"∀ {' '.join(kept_binders)}, {body}"


def query_prover_with_retries(
    worker_settings: Any,
    prover_prompt: str,
    problem_id: str,
    stmt: str,
    original_stmt: str,
    derived_theorems: list[dict[str, str]],
    prover_retry_budget_sec: int | None,
    theory_context: str,
    current_iteration_full_logs: list[dict[str, Any]],
    same_problem_history_tail: list[dict[str, Any]],
    run_id: str,
    session_type: str,
    iteration: int,
    phase_attempts_path: Path,
    max_same_error_streak: int | None = None,
) -> tuple[str, str, str, int, dict[str, Any]]:
    deadline = build_retry_deadline(prover_retry_budget_sec)
    last_response_fingerprint = ""
    same_response_streak = 0
    attempt = 0
    last_worker_meta: dict[str, Any] = {}
    last_response = ProverResponsePacket(
        problem_id=problem_id,
        result="stuck",
        proof_sketch="",
        counterexample_text="",
    )

    while True:
        if deadline is not None and attempt > 0 and time.monotonic() >= deadline:
            break
        attempt += 1
        attempt_worker_meta: dict[str, Any] = {}
        prover_request = ProverRequestPacket(
            problem_id=problem_id,
            stmt=stmt,
            original_stmt=original_stmt,
            derived_theorems=[
                {
                    "name": str(entry.get("name", "")).strip(),
                    "statement": str(entry.get("statement", "")).strip(),
                }
                for entry in derived_theorems
                if str(entry.get("name", "")).strip() and str(entry.get("statement", "")).strip()
            ],
            theory_context=theory_context,
            same_problem_history_tail=same_problem_history_tail,
            retry_round=attempt - 1,
            retry_instruction=(
                "Previous attempt returned stuck. Try a different angle. "
                "If you still cannot prove or refute, return at least one concrete "
                "counterexample candidate in counterexample_text."
            )
            if attempt > 1
            else "",
            previous_result=last_response.result,
            previous_proof_sketch=last_response.proof_sketch,
            previous_counterexample_text=last_response.counterexample_text,
        )

        try:
            debug_log(f"Calling prover for problem {problem_id}, attempt {attempt}")
            prover_started_monotonic = time.monotonic()
            prover_started_at = iso_timestamp_now()
            prover_payload, worker_meta = invoke_worker_json(
                settings=worker_settings,
                task_type="prover",
                system_prompt=prover_prompt,
                payload=prover_request.to_payload(),
                metadata={"problem_id": problem_id, "attempt": attempt},
            )
            attempt_worker_meta = worker_meta
            last_worker_meta = worker_meta
            append_current_iteration_log(
                current_iteration_full_logs,
                stage="prover",
                index=attempt,
                worker_meta=worker_meta,
            )
            prover_finished_at = iso_timestamp_now()
            prover_elapsed = time.monotonic() - prover_started_monotonic
            debug_log(f"Prover returned for {problem_id}: {prover_payload.get('result', 'unknown')} (took {prover_elapsed:.1f}s)")
        except RuntimeError as exc:
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type=session_type,
                iteration=iteration,
                entity_id=problem_id,
                phase="proof_nl",
                worker_task="prover",
                started_at=prover_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(prover_started_monotonic),
                success=False,
                result="timeout" if is_worker_timeout_error(exc) else "error",
                timeout=is_worker_timeout_error(exc),
                error=str(exc),
            )
            if is_worker_timeout_error(exc):
                debug_log(f"Prover timed out for {problem_id}: {exc}")
                timeout_sketch = (
                    "Prover worker timed out before returning a valid response. "
                    "Treating this iteration as stuck so the problem remains open. "
                    f"Details: {exc}"
                )
                return "stuck", timeout_sketch, "", attempt, attempt_worker_meta
            raise
        prover_response = validate_prover_output(prover_payload, problem_id).with_attempt(attempt)
        prover_response = prover_response.with_worker_meta(last_worker_meta)
        result, proof_sketch, counterexample_text, _, _ = prover_response.as_tuple()
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type=session_type,
            iteration=iteration,
            entity_id=problem_id,
            phase="proof_nl",
            worker_task="prover",
            started_at=prover_started_at,
            finished_at=prover_finished_at,
            duration_ms=monotonic_duration_ms(prover_started_monotonic),
            success=result != "stuck",
            result=result,
        )

        last_response = prover_response

        if result != "stuck":
            return result, proof_sketch, counterexample_text, attempt, last_worker_meta

        response_fingerprint = prover_response_fingerprint(
            result=result,
            proof_sketch=proof_sketch,
            counterexample_text=counterexample_text,
        )
        last_response_fingerprint, same_response_streak = update_same_fingerprint_streak(
            last_fingerprint=last_response_fingerprint,
            current_fingerprint=response_fingerprint,
            current_streak=same_response_streak,
        )
        if max_same_error_streak is not None and same_response_streak >= max_same_error_streak:
            break

    return (
        last_response.result,
        last_response.proof_sketch,
        last_response.counterexample_text,
        attempt,
        last_worker_meta,
    )


def request_initial_formalization(
    *,
    formalize_worker_settings: Any,
    formalizer_prompt: str,
    problem_id: str,
    stmt: str,
    result: str,
    proof_sketch: str,
    counterexample_text: str,
    open_rows: list[dict[str, Any]],
    theory_context: str,
    current_iteration_full_logs: list[dict[str, Any]],
    same_problem_history_tail: list[dict[str, Any]],
    retry_round: int = 0,
    retry_instruction: str = "",
    previous_result: str = "",
    previous_prelude_code: str = "",
    previous_proof_text: str = "",
    previous_counterexample_text: str = "",
) -> tuple[str, str, str, str, str]:
    formalizer_request = FormalizerRequestPacket(
        problem_id=problem_id,
        stmt=stmt,
        result=result,
        proof_sketch=proof_sketch,
        counterexample_text=counterexample_text,
        theory_context=theory_context,
        open_rows=open_rows,
        same_problem_history_tail=same_problem_history_tail,
        retry_round=retry_round,
        retry_instruction=retry_instruction,
        previous_result=previous_result,
        previous_prelude_code=previous_prelude_code,
        previous_proof_text=previous_proof_text,
        previous_counterexample_text=previous_counterexample_text,
        mathlib_allowed=True,
    )
    formalized, formalize_worker_meta = invoke_worker_json(
        settings=formalize_worker_settings,
        task_type="formalize",
        system_prompt=formalizer_prompt,
        payload=formalizer_request.to_payload(),
        metadata={"problem_id": problem_id},
    )
    append_current_iteration_log(
        current_iteration_full_logs,
        stage="formalize",
        index=retry_round + 1,
        worker_meta=formalize_worker_meta,
    )
    formalizer_response = validate_formalizer_output(formalized, problem_id)
    return formalizer_response.as_tuple()


def request_prover_statement_formalization(
    *,
    worker_settings: Any,
    prover_statement_prompt: str,
    problem_id: str,
    stmt: str,
    open_rows: list[dict[str, Any]],
    theory_context: str,
    current_iteration_full_logs: list[dict[str, Any]],
    repair_round: int = 0,
    retry_instruction: str = "",
    previous_statement_prelude_code: str = "",
    previous_lean_statement: str = "",
    previous_theorem_name_stem: str = "",
    previous_docstring_summary: str = "",
    previous_notes: str = "",
    lean_error_excerpt: str = "",
    lean_error_top_lines: list[str] | None = None,
    lean_diagnostics: str = "",
    repair_history_tail: list[dict[str, Any]] | None = None,
) -> tuple[str, str, str, str, str, str, dict[str, Any]]:
    statement_payload = SolverStatementRequestPacket(
        problem_id=problem_id,
        stmt=stmt,
        theory_context=theory_context,
        open_rows=open_rows,
        repair_round=repair_round,
        retry_instruction=retry_instruction,
        previous_statement_prelude_code=previous_statement_prelude_code,
        previous_lean_statement=previous_lean_statement,
        previous_theorem_name_stem=previous_theorem_name_stem,
        previous_docstring_summary=previous_docstring_summary,
        previous_notes=previous_notes,
        lean_error_excerpt=lean_error_excerpt,
        lean_error_top_lines=lean_error_top_lines or [],
        lean_diagnostics=lean_diagnostics,
        repair_history_tail=repair_history_tail or [],
    )
    formalized, worker_meta = invoke_worker_json(
            settings=worker_settings,
            task_type="prover_statement",
            system_prompt=prover_statement_prompt,
            payload=statement_payload.to_payload(),
            metadata={"problem_id": problem_id},
        )
    append_current_iteration_log(
        current_iteration_full_logs,
        stage="prover_statement",
        index=repair_round + 1,
        worker_meta=worker_meta,
    )
    try:
        result, statement_prelude_code, lean_statement, theorem_name_stem, docstring_summary, notes = validate_prover_statement_output(
            formalized,
            problem_id,
        )
    except ValueError as exc:
        raw_result = str(formalized.get("result", "")).strip() if isinstance(formalized, dict) else ""
        raw_stmt_prelude = str(formalized.get("statement_prelude_code", "")).strip() if isinstance(formalized, dict) else ""
        raw_stmt = str(formalized.get("lean_statement", "")).strip() if isinstance(formalized, dict) else ""
        raw_docstring = str(formalized.get("docstring_summary", "")).strip() if isinstance(formalized, dict) else ""
        raw_notes = str(formalized.get("notes", "")).strip() if isinstance(formalized, dict) else ""
        raw_stem = str(formalized.get("theorem_name_stem", "")).strip() if isinstance(formalized, dict) else ""
        repair_note = f"Invalid prover_statement output repaired locally: {exc}"
        notes = "\n".join(part for part in (raw_notes, repair_note) if part).strip()
        if raw_result == "ok" and raw_stmt:
            try:
                theorem_name_stem = validate_theorem_name_stem(raw_stem)
            except ValueError:
                theorem_name_stem = "statement_target"
            return "ok", raw_stmt_prelude, raw_stmt, theorem_name_stem, raw_docstring, notes, worker_meta
        return "stuck", "", "", "", "", notes or repair_note, worker_meta
    return result, statement_prelude_code, lean_statement, theorem_name_stem, docstring_summary, notes, worker_meta


def resolve_solver_statement(
    *,
    prover_statement_worker_settings: Any,
    prover_statement_prompt_file: str,
    statement_verify_timeout_sec: int = 180,
    skip_verify: bool = False,
    statement_retry_budget_sec: int | None = None,
    max_same_error_streak: int | None = None,
    phase_logs: bool,
    iteration: int,
    problem_id: str,
    original_stmt: str,
    open_rows: list[dict[str, Any]],
    theory_context: str,
    current_iteration_full_logs: list[dict[str, Any]],
    run_id: str,
    phase_attempts_path: Path,
    compile_metrics: dict[str, Any],
) -> tuple[str, str, str, str, str, str, dict[str, Any]]:
    prover_statement_worker_meta: dict[str, Any] = {}
    prover_statement_prompt = load_prompt_text(prover_statement_prompt_file)
    repair_round = 0
    retry_instruction = ""
    previous_statement_prelude_code = ""
    previous_lean_statement = ""
    previous_theorem_name_stem = ""
    previous_docstring_summary = ""
    previous_notes = ""
    lean_error_excerpt = ""
    lean_error_top_lines: list[str] = []
    lean_diagnostics = ""
    repair_history: list[dict[str, Any]] = []
    last_failure_signature = ""
    same_failure_streak = 0
    deadline = build_retry_deadline(statement_retry_budget_sec)

    while True:
        if deadline is not None and repair_round > 0 and time.monotonic() >= deadline:
            result = "stuck"
            statement_prelude_code = ""
            formalized_stmt = ""
            theorem_name_stem = ""
            docstring_summary = ""
            notes = (
                f"{previous_notes}\nStatement repair budget exhausted before a valid Lean statement was found."
                if previous_notes
                else "Statement repair budget exhausted before a valid Lean statement was found."
            )
            break
        emit_phase_log(
            phase_logs,
            "prover_statement",
            iteration=iteration,
            problem_id=problem_id,
            mode="worker",
            repair_round=repair_round,
        )
        stmt_started_monotonic = time.monotonic()
        stmt_started_at = iso_timestamp_now()
        try:
            (
                result,
                statement_prelude_code,
                formalized_stmt,
                theorem_name_stem,
                docstring_summary,
                notes,
                prover_statement_worker_meta,
            ) = request_prover_statement_formalization(
                worker_settings=prover_statement_worker_settings,
                prover_statement_prompt=prover_statement_prompt,
                problem_id=problem_id,
                stmt=original_stmt,
                open_rows=open_rows,
                theory_context=theory_context,
                current_iteration_full_logs=current_iteration_full_logs,
                repair_round=repair_round,
                retry_instruction=retry_instruction,
                previous_statement_prelude_code=previous_statement_prelude_code,
                previous_lean_statement=previous_lean_statement,
                previous_theorem_name_stem=previous_theorem_name_stem,
                previous_docstring_summary=previous_docstring_summary,
                previous_notes=previous_notes,
                lean_error_excerpt=lean_error_excerpt,
                lean_error_top_lines=lean_error_top_lines,
                lean_diagnostics=lean_diagnostics,
                repair_history_tail=repair_history[-8:],
            )
        except RuntimeError as exc:
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type="loop",
                iteration=iteration,
                entity_id=problem_id,
                phase="stmt",
                worker_task="prover_statement",
                started_at=stmt_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(stmt_started_monotonic),
                success=False,
                result="timeout" if is_worker_timeout_error(exc) else "error",
                timeout=is_worker_timeout_error(exc),
                error=str(exc),
            )
            if not is_worker_timeout_error(exc):
                raise
            result = "stuck"
            statement_prelude_code = ""
            formalized_stmt = ""
            theorem_name_stem = ""
            docstring_summary = ""
            notes = f"prover_statement worker timeout: {exc}"
            break

        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type="loop",
            iteration=iteration,
            entity_id=problem_id,
            phase="stmt",
            worker_task="prover_statement",
            started_at=stmt_started_at,
            finished_at=iso_timestamp_now(),
            duration_ms=monotonic_duration_ms(stmt_started_monotonic),
            success=result == "ok",
            result=result,
        )
        emit_parse_phase_log(
            phase_logs,
            "prover_statement_parse",
            iteration=iteration,
            problem_id=problem_id,
            worker_meta=prover_statement_worker_meta,
            repair_round=repair_round,
        )

        if result != "ok":
            break

        theorem_name = build_theorem_name(problem_id, theorem_name_stem)
        verify_started_monotonic = time.monotonic()
        verify_started_at = iso_timestamp_now()
        compactness_issue = analyze_lean_statement_compactness(
            formalized_stmt,
            statement_prelude_code=statement_prelude_code,
        )
        if compactness_issue is not None:
            verify_success = False
            verify_result = {
                "success": False,
                "stdout": compactness_issue["message"],
                "stderr": "",
                "duration_ms": 0,
                "error_category": ["statement_compactness"],
                "diagnostics": compactness_issue["diagnostics"],
            }
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type="loop",
                iteration=iteration,
                entity_id=problem_id,
                phase="verify",
                worker_task="stmt_compactness",
                started_at=verify_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=0,
                success=False,
                result="failed",
                error=compactness_issue["message"],
            )
        elif skip_verify:
            verify_success = True
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type="loop",
                iteration=iteration,
                entity_id=problem_id,
                phase="verify",
                worker_task="stmt_check",
                started_at=verify_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(verify_started_monotonic),
                success=True,
                result="skipped",
            )
        else:
            verify_result = validate_solver_statement_with_lean(
                problem_id=problem_id,
                theorem_name=theorem_name,
                stmt=formalized_stmt,
                statement_prelude_code=statement_prelude_code,
                timeout_sec=statement_verify_timeout_sec,
            )
            update_compile_metrics(compile_metrics, verify_result)
            verify_success = bool(verify_result.get("success", False))
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type="loop",
                iteration=iteration,
                entity_id=problem_id,
                phase="verify",
                worker_task="stmt_check",
                started_at=verify_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=int(verify_result.get("duration_ms", monotonic_duration_ms(verify_started_monotonic)) or 0),
                success=verify_success,
                result="verified" if verify_success else "failed",
            )
        if verify_success:
            break

        lean_stderr = str(verify_result.get("stderr", "")).strip()
        lean_stdout = str(verify_result.get("stdout", "")).strip()
        lean_excerpt = (lean_stderr or lean_stdout).splitlines()[0] if (lean_stderr or lean_stdout) else "Lean statement validation failed"
        error_analysis = analyze_lean_failure(
            lean_stderr,
            lean_stdout,
            verify_result=verify_result,
        )
        error_fingerprint = str(error_analysis.get("fingerprint", "no_diagnostics"))
        failure_signature = f"{normalize_stmt_text(formalized_stmt)} || {error_fingerprint}"
        last_failure_signature, same_failure_streak = update_same_fingerprint_streak(
            last_fingerprint=last_failure_signature,
            current_fingerprint=failure_signature,
            current_streak=same_failure_streak,
        )

        if compactness_issue is not None:
            lean_failure_note = compactness_issue["message"]
        else:
            lean_failure_note = f"Lean statement validation failed before proof search: {lean_excerpt}"
        notes = "\n".join(part for part in (notes, lean_failure_note) if part).strip()
        repair_history.append(
            {
                "repair_round": repair_round,
                "statement_prelude_code": statement_prelude_code,
                "lean_statement": formalized_stmt,
                "theorem_name_stem": theorem_name_stem,
                "docstring_summary": docstring_summary,
                "notes": notes,
                "lean_error_excerpt": lean_excerpt,
                "lean_error_fingerprint": error_fingerprint,
            }
        )
        if len(repair_history) > 20:
            repair_history = repair_history[-20:]

        emit_phase_log(
            phase_logs,
            "prover_statement_repair",
            iteration=iteration,
            problem_id=problem_id,
            repair_round=repair_round + 1,
            error_fingerprint=error_fingerprint,
            theorem_name_stem=theorem_name_stem,
        )
        if max_same_error_streak is not None and same_failure_streak >= max_same_error_streak:
            result = "stuck"
            statement_prelude_code = ""
            formalized_stmt = ""
            theorem_name_stem = ""
            docstring_summary = ""
            notes = (
                f"{notes}\nStatement repair stopped after repeated identical stmt_check failures."
                if notes
                else "Statement repair stopped after repeated identical stmt_check failures."
            )
            break

        if compactness_issue is not None:
            retry_instruction = compactness_issue["retry_instruction"]
        else:
            retry_instruction = (
                "Previous statement_prelude_code and lean_statement failed Lean statement validation before proof search. "
                "Keep the mathematical meaning of `stmt`, but repair the Lean declarations and proposition minimally. "
                "Prioritize parser, binder, notation, and namespace fixes. "
                "Return only statement_prelude_code plus one proposition statement, not a theorem or proof."
            )
        previous_statement_prelude_code = statement_prelude_code
        previous_lean_statement = formalized_stmt
        previous_theorem_name_stem = theorem_name_stem
        previous_docstring_summary = docstring_summary
        previous_notes = notes
        lean_error_excerpt = lean_excerpt
        lean_error_top_lines = [str(line).strip() for line in error_analysis.get("top_lines", []) if str(line).strip()]
        lean_diagnostics = "\n".join(
            (lean_stderr + "\n" + lean_stdout).splitlines()[:60]
        ).strip()
        repair_round += 1

    solver_stmt = formalized_stmt if result == "ok" else ""
    emit_phase_log(
        phase_logs,
        "prover_statement_result",
        iteration=iteration,
        problem_id=problem_id,
        formalized=result == "ok",
        theorem_name_stem=theorem_name_stem,
        notes=notes,
        repair_round=repair_round,
    )
    return (
        solver_stmt,
        statement_prelude_code if result == "ok" else "",
        result,
        theorem_name_stem,
        docstring_summary,
        notes,
        prover_statement_worker_meta,
    )


def request_expand_candidates(
    *,
    worker_settings: Any,
    expand_prompt: str,
    task_type: str,
    problem_id: str,
    stmt: str,
    original_stmt: str,
    result: str,
    verify_success: bool,
    theory_context: str,
    open_rows: list[dict[str, Any]],
    existing_new_problems: list[str],
    verify_error_excerpt: str,
    current_iteration_full_logs: list[dict[str, Any]],
    same_problem_history_tail: list[dict[str, Any]],
    theory_state: dict[str, Any] | None = None,
    materials: dict[str, Any] | None = None,
    max_candidates: int = 3,
) -> tuple[list[dict[str, str]], dict[str, Any]]:
    expand_payload: dict[str, Any] = {
        "problem_id": problem_id,
        "stmt": stmt,
        "original_stmt": original_stmt,
        "result": result,
        "verify_success": verify_success,
        "theory_context": theory_context,
        "open_problems": open_rows,
        "existing_new_problems": list(existing_new_problems),
        "verify_error_excerpt": verify_error_excerpt,
        "current_iteration_full_logs": list(current_iteration_full_logs),
        "same_problem_history_tail": same_problem_history_tail,
        "theory_state": dict(theory_state or {}),
        "research_agenda": load_current_research_agenda(),
        "materials": dict(load_current_materials() if materials is None else materials),
        "expand_generation_policy": {
            "prefer_subgoals_for_unsolved": True,
            "avoid_generalization_for_unsolved": True,
            "prefer_same_problem_decomposition": True,
            "prefer_intermediate_lemmas": True,
        },
    }
    expanded, expand_worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type=task_type,
        system_prompt=expand_prompt,
        payload=expand_payload,
        metadata={"problem_id": problem_id},
    )
    append_current_iteration_log(
        current_iteration_full_logs,
        stage="expand",
        index=1,
        worker_meta=expand_worker_meta,
    )
    return validate_problem_candidates_output(
        expanded,
        expected_problem_id=problem_id,
        max_candidates=max_candidates,
    ), expand_worker_meta


def request_open_problem_priorities(
    *,
    worker_settings: Any,
    prioritizer_prompt: str,
    tracked_rows: list[dict[str, Any]],
    derived_entries: list[dict[str, str]],
    current_iteration: int,
    guidance: dict[str, Any],
) -> tuple[list[dict[str, str]], str, dict[str, str], dict[str, list[str]], dict[str, Any]]:
    previous_theory_state, research_agenda, materials = unpack_guidance_context(guidance)
    expected_problem_ids = [str(row.get("id", "")) for row in tracked_rows]
    priority_payload: dict[str, Any] = {
        "current_iteration": current_iteration,
        "tracked_problems": [
            {
                "problem_id": str(row.get("id", "")),
                "stmt": str(row.get("stmt", "")),
                "src": str(row.get("src", "")),
                "source_kind": str(row.get("source_kind", row.get("queue_status", "open"))),
                "queue_status": str(row.get("queue_status", row.get("source_kind", "open"))),
                "mode": str(row.get("mode", "")),
                "summary_delta": str(row.get("summary_delta", "")),
            }
            for row in tracked_rows
        ],
        "derived_theorems": [
            {
                "name": str(entry.get("name", "")),
                "statement": str(entry.get("statement", "")),
            }
            for entry in derived_entries
        ],
        "priority_rubric": {
            "high": "Connects existing clusters, gives a strong equivalence/characterization/existence theorem, or is likely to unlock many future problems.",
            "medium": "Natural local extension with plausible reuse for one or two nearby problems.",
            "low": "Cosmetic variant, shallow restatement, or currently low-utility statement given the present Derived.lean.",
        },
        "previous_theory_state": previous_theory_state,
        "research_agenda": research_agenda,
        "materials": materials,
    }
    prioritized, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="prioritize_open_problems",
        system_prompt=prioritizer_prompt,
        payload=priority_payload,
        metadata={"tracked_problem_count": len(tracked_rows), "derived_theorem_count": len(derived_entries)},
    )
    priority_updates, theory_snapshot, next_direction, theory_frontier = validate_open_problem_priority_output(
        prioritized,
        expected_problem_ids,
    )
    return priority_updates, theory_snapshot, next_direction, theory_frontier, worker_meta


def force_refresh_open_problem_priorities(
    *,
    data_dir: Path,
    worker_settings: Any,
    prioritizer_prompt_file: str,
    derived_entries: list[dict[str, str]],
    current_iteration: int,
    failure_threshold: int,
    run_id: str,
    theory_state_history_path: Path | None = None,
) -> tuple[bool, str, dict[str, Any]]:
    open_path = loop_open_problems_path(data_dir)
    archived_path = loop_archived_problems_path(data_dir)
    open_rows = [normalize_open_problem_row(row) for row in read_jsonl(open_path)]
    archived_rows = read_archived_problem_rows(data_dir)
    tracked_rows = [
        dict(row, queue_status="open", source_kind=str(row.get("source_kind", "open") or "open"))
        for row in open_rows
    ]
    tracked_rows.extend(
        dict(row, queue_status="archived", source_kind=str(row.get("source_kind", "archived") or "archived"))
        for row in archived_rows
    )
    if not tracked_rows:
        return False, "", {}

    prioritizer_prompt = load_prompt_text(prioritizer_prompt_file)
    guidance = load_current_guidance(data_dir)
    try:
        (
            priority_updates,
            theory_snapshot,
            next_direction,
            theory_frontier,
            worker_meta,
        ) = request_open_problem_priorities(
            worker_settings=worker_settings,
            prioritizer_prompt=prioritizer_prompt,
            tracked_rows=tracked_rows,
            derived_entries=derived_entries,
            current_iteration=current_iteration,
            guidance=guidance,
        )
    except (RuntimeError, ValueError) as exc:
        return False, str(exc), {}

    refreshed_open_rows = apply_open_problem_priorities(open_rows, priority_updates)
    refreshed_archived_rows = apply_open_problem_priorities(archived_rows, priority_updates)
    refreshed_open_rows, newly_archived_rows = split_active_and_archived_problem_queues(
        refreshed_open_rows,
        failure_archive_threshold=failure_threshold,
    )
    refreshed_archived_rows = merge_archived_problem_rows(refreshed_archived_rows, newly_archived_rows)
    refreshed_open_rows = sort_open_problem_queue(
        dedupe_problem_rows_by_stmt(refreshed_open_rows),
        failure_archive_threshold=failure_threshold,
    )
    important_verified_counterexamples = collect_important_verified_counterexamples(data_dir)
    write_jsonl_atomic(open_path, refreshed_open_rows)
    write_jsonl_atomic(archived_path, refreshed_archived_rows)
    theory_state = write_theory_state(
        data_dir,
        run_id=run_id,
        current_iteration=current_iteration,
        derived_theorem_count=len(derived_entries),
        open_problem_count=len(refreshed_open_rows),
        archived_problem_count=len(refreshed_archived_rows),
        theory_snapshot=theory_snapshot,
        next_direction=next_direction,
        important_verified_counterexamples=important_verified_counterexamples,
        research_agenda_summary=summarize_research_agenda_for_state(guidance["research_agenda"]),
        theory_frontier=theory_frontier,
    )
    if theory_state_history_path is not None:
        append_theory_state_history(
            theory_state_history_path,
            run_id=run_id,
            current_iteration=current_iteration,
            theory_state=theory_state,
        )
    return True, "", {
        **dict(worker_meta),
        "promoted_expand_rows": [],
        "remaining_expand_rows": [],
    }


def run_batch_generator_subprocess(
    *,
    repo_root: Path,
    theory_file: Path,
    derived_file: Path,
    output_file: Path,
    seed_count: int,
) -> tuple[list[dict[str, Any]], str]:
    script_path = (SCRIPTS_ROOT / "generate_seeds_from_theory.py").resolve()
    cmd = [
        sys.executable,
        str(script_path),
        "--theory-file",
        str(theory_file),
        "--derived-file",
        str(derived_file),
        "--output-file",
        str(output_file),
        "--seed-count",
        str(seed_count),
        "--seed-src",
        "batch_generator",
        "--no-initialize-runtime-state",
        "--repo-root",
        str(repo_root),
    ]
    completed = subprocess.run(
        cmd,
        cwd=str(repo_root),
        capture_output=True,
        text=True,
    )
    if completed.returncode != 0:
        stderr = (completed.stderr or "").strip()
        stdout = (completed.stdout or "").strip()
        return [], stderr or stdout or f"batch generator exited with code {completed.returncode}"
    return read_jsonl(output_file), ""


def maybe_backfill_open_problems_from_batch_generator(
    *,
    data_dir: Path,
    repo_root: Path,
    theory_file: Path,
    derived_file: Path,
    open_problem_target_min: int,
    seed_count: int,
    reserved_problem_ids: set[str] | None = None,
    phase_logger: Callable[..., None] | None = None,
) -> tuple[list[dict[str, Any]], str]:
    open_path = loop_open_problems_path(data_dir)
    open_rows = [normalize_open_problem_row(row) for row in read_jsonl(open_path)]
    reserved_ids = set(reserved_problem_ids or set())
    available_open_rows = [
        row
        for row in open_rows
        if str(row.get("id", "")).strip() and str(row.get("id", "")).strip() not in reserved_ids
    ]
    if (
        open_problem_target_min > 0
        and len(available_open_rows) >= open_problem_target_min
        and any(open_problem_priority_label(row) == "unknown" for row in available_open_rows)
    ):
        # During bootstrap, seeded problems often start as `unknown` until the
        # prioritizer runs. Treat those as pending work rather than a signal to
        # synthesize more problems immediately.
        return [], ""
    if has_available_solver_eligible_problem(open_rows, reserved_problem_ids=reserved_ids):
        return [], ""

    archived_rows = read_archived_problem_rows(data_dir)
    solved_rows = read_jsonl(loop_solved_problems_path(data_dir))
    counter_rows = read_jsonl(loop_counterexamples_path(data_dir))
    seen_norms = {
        normalize_stmt_text(str(row.get("stmt", "")))
        for row in (open_rows + archived_rows + solved_rows + counter_rows)
        if str(row.get("stmt", "")).strip()
    }
    all_ids = [str(row.get("id", "")) for row in open_rows + archived_rows + solved_rows + counter_rows]
    requested_count = seed_count
    if requested_count <= 0:
        return [], ""

    if phase_logger is not None:
        phase_logger(
            phase="batch_seed_generation",
            status="begin",
            requested_seed_count=requested_count,
            active_open_problem_count=len(open_rows),
            reserved_problem_count=len(reserved_ids),
        )

    with tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        suffix=".jsonl",
        prefix="batch_generator_",
        delete=False,
        dir=str(data_dir),
    ) as handle:
        output_file = Path(handle.name)

    try:
        generated_rows, error = run_batch_generator_subprocess(
            repo_root=repo_root,
            theory_file=theory_file,
            derived_file=derived_file,
            output_file=output_file,
            seed_count=requested_count,
        )
        if error:
            if phase_logger is not None:
                phase_logger(
                    phase="batch_seed_generation",
                    status="error",
                    requested_seed_count=requested_count,
                    error=error,
                )
            return [], error

        added_rows: list[dict[str, Any]] = []
        for row in generated_rows:
            stmt = str(row.get("stmt", "")).strip()
            if not stmt:
                continue
            norm = normalize_stmt_text(stmt)
            if not norm or norm in seen_norms:
                continue
            new_id = next_problem_id(all_ids)
            all_ids.append(new_id)
            seen_norms.add(norm)
            new_row = normalize_open_problem_row(
                {
                    **dict(row),
                    "id": new_id,
                    "src": str(row.get("src", "batch_generator") or "batch_generator").strip() or "batch_generator",
                    "priority": "unknown",
                    "priority_rationale": "",
                    "failure_count": 0,
                }
            )
            open_rows.append(new_row)
            added_rows.append(dict(new_row))

        if added_rows:
            write_jsonl_atomic(open_path, dedupe_problem_rows_by_stmt(open_rows))
        if phase_logger is not None:
            phase_logger(
                phase="batch_seed_generation",
                status="result",
                requested_seed_count=requested_count,
                generated_count=len(generated_rows),
                added_count=len(added_rows),
            )
        return added_rows, ""
    finally:
        output_file.unlink(missing_ok=True)


def backfill_open_problems_if_needed(
    *,
    data_dir: Path,
    theory_file: Path,
    derived_file: Path,
    repo_root: Path,
    batch_generator_seed_count: int,
    batch_generator_open_target_min: int,
    reserved_problem_ids: set[str] | None = None,
    phase_logger: Callable[..., None] | None = None,
) -> tuple[bool, str, dict[str, Any]]:
    added_rows, batch_error = maybe_backfill_open_problems_from_batch_generator(
        data_dir=data_dir,
        repo_root=repo_root,
        theory_file=theory_file,
        derived_file=derived_file,
        open_problem_target_min=batch_generator_open_target_min,
        seed_count=batch_generator_seed_count,
        reserved_problem_ids=reserved_problem_ids,
        phase_logger=phase_logger,
    )
    return bool(added_rows), batch_error, {
        "batch_generator_added_problem_rows": added_rows,
        "batch_generator_error": batch_error,
    }


def initialize_runtime_state(
    data_dir: Path,
    seeds_file: Path,
    scratch_file: Path,
    reset_scratch: bool,
    derived_file: Path,
    derived_cleanup_files: tuple[Path, ...],
    reset_derived: bool,
    formalization_memory_file: Path,
    reset_formalization_memory: bool,
    archived_problems_file: Path,
) -> None:
    seed_rows = dedupe_problem_rows_by_stmt(
        [normalize_open_problem_row(row) for row in read_jsonl(seeds_file)]
    )
    if not seed_rows:
        raise ValueError(f"Seeds file is empty: {seeds_file}")

    reset_loop_runtime_data(
        data_dir=data_dir,
        derived_file=derived_file,
        open_problem_rows=seed_rows,
        archived_problems_file=archived_problems_file,
        clear_paper_claim_rejection_memory=True,
    )
    reset_loop_work_files(
        scratch_file=scratch_file,
        cleanup_parallel_scratch_files=cleanup_parallel_scratch_files,
        reset_scratch=reset_scratch,
        scratch_template=SCRATCH_TEMPLATE,
        derived_file=derived_file,
        derived_cleanup_files=derived_cleanup_files,
        reset_derived=reset_derived,
        derived_template=DERIVED_TEMPLATE,
        formalization_memory_file=formalization_memory_file,
        reset_formalization_memory=reset_formalization_memory,
    )


def capture_continuation_runtime_snapshot(
    *,
    data_dir: Path,
    formalization_memory_file: Path,
    scratch_file: Path,
    derived_file: Path,
    derived_cleanup_files: tuple[Path, ...],
) -> dict[str, str | int | None]:
    tracked_paths = (
        loop_open_problems_path(data_dir),
        loop_archived_problems_path(data_dir),
        loop_solved_problems_path(data_dir),
        loop_counterexamples_path(data_dir),
        loop_theorem_reuse_memory_path(data_dir),
        loop_paper_claim_rejection_memory_path(data_dir),
        theory_state_path(data_dir),
        formalization_memory_file,
        scratch_file,
        derived_file,
        *derived_cleanup_files,
    )
    snapshot: dict[str, str | int | None] = {
        "__history_row_total__": sum(
            len(read_jsonl(path))
            for path in (
                loop_archived_problems_path(data_dir),
                loop_solved_problems_path(data_dir),
                loop_counterexamples_path(data_dir),
            )
        )
    }
    for path in tracked_paths:
        snapshot[str(path.resolve())] = path.read_text(encoding="utf-8") if path.exists() else None
    return snapshot


def restore_continuation_runtime_snapshot(snapshot: dict[str, str | int | None]) -> None:
    for raw_path, content in snapshot.items():
        if raw_path.startswith("__"):
            continue
        path = Path(raw_path)
        if content is None:
            path.unlink(missing_ok=True)
            continue
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(str(content), encoding="utf-8")


def guard_against_unexpected_continuation_reset(
    *,
    data_dir: Path,
    snapshot: dict[str, str | int | None] | None,
) -> None:
    if snapshot is None:
        return
    before_history_total = int(snapshot.get("__history_row_total__", 0) or 0)
    if before_history_total <= 0:
        return
    after_history_total = sum(
        len(read_jsonl(path))
        for path in (
            loop_archived_problems_path(data_dir),
            loop_solved_problems_path(data_dir),
            loop_counterexamples_path(data_dir),
        )
    )
    if after_history_total != 0:
        return
    restore_continuation_runtime_snapshot(snapshot)
    raise RuntimeError(
        "Continuation run unexpectedly cleared archived/solved/counterexample state; restored the pre-run snapshot. "
        "This usually means an initialization/reset path ran during a supposed continuation run."
    )


def run_problem_session(
    *,
    args: Any,
    picked: dict[str, Any],
    open_rows: list[dict[str, Any]],
    base_theory_context: str,
    derived_entries_snapshot: list[dict[str, str]],
    shared_derived_entries: list[dict[str, str]],
    data_dir: Path,
    memory_path: Path,
    derived_path: Path,
    current_iteration: int,
    run_id: str,
    artifact_paths: dict[str, Path],
    compile_metrics: dict[str, Any],
    worker_settings: Any,
    prover_worker_settings: Any,
    prover_statement_worker_settings: Any,
    formalize_worker_settings: Any,
    repair_worker_settings: Any,
    prioritize_open_problems_worker_settings: Any,
    state_lock: threading.Lock,
    derived_runtime_state: dict[str, Any],
    scratch_file: Path,
) -> dict[str, Any]:
    debug_log(f"=== Iteration {current_iteration} START ===")
    debug_log(f"Session picked problem {picked.get('id', '')}")

    problem_id = str(picked["id"])
    original_stmt = str(picked.get("stmt", ""))
    initial_theory_context = build_problem_theory_context(base_theory_context, derived_entries_snapshot, original_stmt)
    emit_phase_log(args.phase_logs, "problem_selected", iteration=current_iteration, problem_id=problem_id)

    current_iteration_full_logs: list[dict[str, Any]] = []
    (
        solver_stmt,
        statement_prelude_code,
        statement_formalization_result,
        theorem_name_stem,
        docstring_summary,
        statement_formalization_notes,
        prover_statement_worker_meta,
    ) = resolve_solver_statement(
        prover_statement_worker_settings=prover_statement_worker_settings,
        prover_statement_prompt_file=PROVER_STATEMENT_PROMPT_FILE,
        skip_verify=args.skip_verify,
        statement_retry_budget_sec=args.formalization_retry_budget_sec,
        max_same_error_streak=args.max_same_error_streak,
        phase_logs=args.phase_logs,
        iteration=current_iteration,
        problem_id=problem_id,
        original_stmt=original_stmt,
        open_rows=open_rows,
        theory_context=initial_theory_context,
        current_iteration_full_logs=current_iteration_full_logs,
        run_id=run_id,
        phase_attempts_path=artifact_paths["phase_attempts"],
        compile_metrics=compile_metrics,
    )
    target_stmt = solver_stmt or original_stmt
    theorem_name = build_theorem_name(problem_id, theorem_name_stem) if solver_stmt else None

    append_formalization_memory_entry(
        memory_path,
        problem_id,
        {
            "stage": "statement_formalization",
            "source_statement": original_stmt,
            "statement_prelude_code": statement_prelude_code,
            "formalized_statement": solver_stmt,
            "theorem_name_stem": theorem_name_stem,
            "docstring_summary": docstring_summary,
            "statement_formalization_notes": statement_formalization_notes,
            "result": statement_formalization_result,
            "verify_success": bool(solver_stmt),
            "proof_sketch": "",
            "proof_text": "",
            "counterexample_text": "",
            "lean_error_excerpt": "",
            "lean_error_fingerprint": "statement_formalization",
        },
    )
    same_problem_history_tail = load_formalization_memory(memory_path, problem_id)[-8:]

    theory_context = build_problem_theory_context(
        base_theory_context,
        derived_entries_snapshot,
        target_stmt,
    )
    prover_derived_theorems = [
        {
            "name": str(entry.get("name", "")).strip(),
            "statement": str(entry.get("statement", "")).strip(),
        }
        for entry in shortlist_relevant_derived_entries(
            derived_entries_snapshot,
            target_stmt,
            max_entries=3,
        )
    ]

    prover_attempts_used = 1
    proof_sketch = ""
    proof_text = ""
    counterexample_text = ""
    prover_worker_meta: dict[str, Any] = {}
    if not solver_stmt:
        result = "stuck"
        proof_sketch = statement_formalization_notes or "Statement formalization failed before proof search."
        counterexample_text = ""
    else:
        emit_phase_log(args.phase_logs, "prover", iteration=current_iteration, problem_id=problem_id, mode="worker")
        prover_prompt = load_prompt_text(PROVER_PROMPT_FILE)
        result, proof_sketch, counterexample_text, prover_attempts_used, prover_worker_meta = query_prover_with_retries(
            worker_settings=prover_worker_settings,
            prover_prompt=prover_prompt,
            problem_id=problem_id,
            stmt=solver_stmt,
            original_stmt=original_stmt,
            derived_theorems=prover_derived_theorems,
            prover_retry_budget_sec=args.prover_retry_budget_sec,
            theory_context=theory_context,
            current_iteration_full_logs=current_iteration_full_logs,
            same_problem_history_tail=same_problem_history_tail,
            run_id=run_id,
            session_type="loop",
            iteration=current_iteration,
            phase_attempts_path=artifact_paths["phase_attempts"],
            max_same_error_streak=args.max_same_error_streak,
        )
        emit_parse_phase_log(
            args.phase_logs,
            "worker_parse",
            iteration=current_iteration,
            problem_id=problem_id,
            worker_meta=prover_worker_meta,
        )

    formalizer_prompts = {
        "proof": load_prompt_text(FORMALIZER_PROOF_PROMPT_FILE),
        "counterexample": load_prompt_text(FORMALIZER_COUNTEREXAMPLE_PROMPT_FILE),
    }
    repair_prompts = {
        "proof": load_prompt_text(REPAIR_PROOF_PROMPT_FILE),
        "counterexample": load_prompt_text(REPAIR_COUNTEREXAMPLE_PROMPT_FILE),
    }
    formalization_deadline = build_retry_deadline(args.formalization_retry_budget_sec)
    theorem_code = ""
    prelude_code = ""
    (
        verify_success,
        theorem_name,
        result,
        prelude_code,
        proof_text,
        counterexample_text,
        verify_error_excerpt,
        target_stmt,
    ) = attempt_formalization_until_timeout(
        problem_id=problem_id,
        theorem_name=theorem_name or build_theorem_name(problem_id, "statement_target"),
        stmt=target_stmt,
        result=result,
        proof_sketch=proof_sketch,
        counterexample_text=counterexample_text,
        scratch_file=scratch_file,
        skip_verify=args.skip_verify,
        formalize_worker_settings=formalize_worker_settings,
        repair_worker_settings=repair_worker_settings,
        formalizer_prompts=formalizer_prompts,
        repair_prompts=repair_prompts,
        open_rows=open_rows,
        theory_context=theory_context,
        verify_timeout_sec=180,
        formalization_retry_budget_sec=remaining_retry_budget_sec(formalization_deadline),
        memory_path=memory_path,
        current_iteration_full_logs=current_iteration_full_logs,
        initial_prelude_code=prelude_code,
        initial_proof_text=proof_text,
        phase_logger=(lambda **fields: emit_phase_log(args.phase_logs, iteration=current_iteration, **fields)),
        max_same_error_streak=args.max_same_error_streak,
        run_id=run_id,
        session_type="loop",
        iteration=current_iteration,
        phase_attempts_path=artifact_paths["phase_attempts"],
        compile_metrics=compile_metrics,
    )

    theorem_context_entries = [dict(entry) for entry in derived_entries_snapshot]
    if should_generate_expand_candidates(verify_success=verify_success, result=result):
        theorem_code = extract_theorem_code_from_scratch(scratch_file)
        if theorem_code:
            append_derived_entry_cache(theorem_context_entries, theorem_code)
            theory_context = build_problem_theory_context(
                base_theory_context,
                theorem_context_entries,
                target_stmt,
            )

    expander_candidates: list[dict[str, str]] = []
    same_problem_history_tail = load_formalization_memory(memory_path, problem_id)[-8:]
    if should_generate_expand_candidates(verify_success=verify_success, result=result):
        expand_started_monotonic = time.monotonic()
        expand_started_at = iso_timestamp_now()
        emit_phase_log(
            args.phase_logs,
            "expand_generate",
            iteration=current_iteration,
            problem_id=problem_id,
            mode="worker",
        )
        try:
            expander_candidates, _ = request_expand_candidates(
                worker_settings=worker_settings,
                expand_prompt=load_prompt_text(EXPANDER_SOLVED_PROOF_PROMPT_FILE),
                task_type="expand",
                problem_id=problem_id,
                stmt=target_stmt,
                original_stmt=original_stmt,
                result=result,
                verify_success=verify_success,
                theory_context=theory_context,
                open_rows=open_rows,
                existing_new_problems=[],
                verify_error_excerpt=verify_error_excerpt,
                current_iteration_full_logs=current_iteration_full_logs,
                same_problem_history_tail=same_problem_history_tail,
                theory_state=load_theory_state(data_dir),
                max_candidates=MAX_EXPAND_CANDIDATES_PER_SOLVED_PROOF,
            )
            append_phase_attempt_record(
                artifact_paths["phase_attempts"],
                run_id=run_id,
                session_type="loop",
                iteration=current_iteration,
                entity_id=problem_id,
                phase="expand",
                worker_task="expand",
                started_at=expand_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(expand_started_monotonic),
                success=True,
                result="ok",
            )
            emit_phase_log(
                args.phase_logs,
                "expand_generate_result",
                iteration=current_iteration,
                problem_id=problem_id,
                generated_count=len(expander_candidates),
            )
        except (RuntimeError, ValueError) as exc:
            append_phase_attempt_record(
                artifact_paths["phase_attempts"],
                run_id=run_id,
                session_type="loop",
                iteration=current_iteration,
                entity_id=problem_id,
                phase="expand",
                worker_task="expand",
                started_at=expand_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(expand_started_monotonic),
                success=False,
                result="error",
                error=str(exc),
            )
            debug_log(f"Expand failed for {problem_id}: {exc}")
            emit_phase_log(
                args.phase_logs,
                "expand_generate_error",
                iteration=current_iteration,
                problem_id=problem_id,
                error=str(exc),
            )

    with state_lock:
        if is_verified_resolution(verify_success=verify_success, result=result):
            theorem_code = commit_verified_theorem_and_generation(
                scratch_path=scratch_file,
                derived_file=derived_path,
                derived_entries=shared_derived_entries,
                docstring=build_theorem_docstring(
                    problem_id=problem_id,
                    docstring_summary=docstring_summary,
                    theorem_name_stem=theorem_name_stem,
                    statement_formalization_notes=statement_formalization_notes,
                ),
                data_dir=data_dir,
                derived_runtime_state=derived_runtime_state,
                run_id=run_id,
                current_iteration=current_iteration,
                rebuild_derived=not args.skip_verify,
            )
            theorem_appended = bool(theorem_code)
        else:
            theorem_appended = False
            theorem_code = ""

        state_update_report = apply_state_update(
            data_dir=data_dir,
            problem_id=problem_id,
            result=result,
            verify_success=verify_success,
            theorem_name=theorem_name,
            result_metadata={
                "run_id": run_id,
                "iteration": current_iteration,
                "session_type": "loop",
            },
            failure_threshold=args.open_problem_failure_threshold,
            current_iteration=current_iteration,
        )
        refresh_outcome = store_expand_candidates_and_refresh(
            data_dir=data_dir,
            statements_with_rationale=expander_candidates,
            source="expand",
            source_problem_id=problem_id,
            source_kind="open_problem",
            prioritize_worker_settings=prioritize_open_problems_worker_settings,
            prioritizer_prompt_file=PRIORITIZE_OPEN_PROBLEMS_PROMPT_FILE,
            derived_entries=shared_derived_entries,
            current_iteration=current_iteration,
            failure_threshold=args.open_problem_failure_threshold,
            run_id=run_id,
            theory_state_history_path=artifact_paths["theory_state_history"],
            theory_file=Path(THEORY_FILE_PATH),
            derived_file=derived_path,
            repo_root=REPO_ROOT,
            batch_generator_seed_count=args.seed_count,
            batch_generator_open_target_min=BATCH_GENERATOR_OPEN_TARGET_MIN,
            allow_backfill=False,
            phase_logger=(lambda **fields: emit_phase_log(args.phase_logs, iteration=current_iteration, **fields)),
        )
        stored_expand_rows = list(refresh_outcome.get("stored_expand_rows", []))
        priority_refresh_ran = bool(refresh_outcome.get("priority_refresh_ran", False))
        priority_refresh_error = str(refresh_outcome.get("priority_refresh_error", ""))
        priority_refresh_report = dict(refresh_outcome.get("priority_refresh_report", {}))
        final_open_rows = [normalize_open_problem_row(row) for row in read_jsonl(loop_open_problems_path(data_dir))]
        final_archived_rows = read_archived_problem_rows(data_dir)
        final_expand_rows = [
            row
            for row in final_open_rows
            if str(row.get("source_kind", "")).strip() == "expand_candidate"
        ]

    emit_phase_log(args.phase_logs, "state_update", iteration=current_iteration, problem_id=problem_id)
    debug_log(f"=== Iteration {current_iteration} END ({result}, verify={verify_success}) ===\n")

    report = dict(state_update_report)
    report["picked_problem_id"] = problem_id
    report["picked_problem_priority"] = open_problem_priority_label(picked)
    report["result"] = result
    report["verify_success"] = verify_success
    report["verify_error_excerpt"] = verify_error_excerpt
    report["original_stmt"] = original_stmt
    report["statement_prelude_code"] = statement_prelude_code
    report["formalized_stmt"] = target_stmt if solver_stmt else ""
    report["prelude_code"] = prelude_code
    report["prover_statement_result"] = statement_formalization_result
    report["prover_attempts_used"] = prover_attempts_used
    report["priority_refresh_ran"] = priority_refresh_ran
    report["priority_refresh_error"] = priority_refresh_error
    report["expand_candidates"] = expander_candidates
    report["stored_expand_rows"] = stored_expand_rows
    report["promoted_expand_rows"] = list(priority_refresh_report.get("worker_meta", {}).get("promoted_expand_rows", [])) if priority_refresh_ran else []
    report["batch_generator_added_problem_rows"] = list(priority_refresh_report.get("batch_generator_added_problem_rows", [])) if priority_refresh_ran else []
    report["batch_generator_error"] = str(priority_refresh_report.get("batch_generator_error", "")) if priority_refresh_ran else ""
    report["pending_expand_candidate_count"] = len(final_expand_rows)
    report["archived_problem_count"] = len(final_archived_rows)
    report["active_open_problem_count"] = len(final_open_rows)
    report["iteration"] = current_iteration

    return {
        "kind": "problem",
        "iteration": current_iteration,
        "problem_id": problem_id,
        "picked": dict(picked),
        "report": report,
        "state_update_report": state_update_report,
        "theorem_appended": theorem_appended,
        "theorem_name": theorem_name,
        "target_stmt": target_stmt,
    }


def run_parallel_loop(
    *,
    args: Any,
    data_dir: Path,
    scratch_file: Path,
    memory_path: Path,
    derived_path: Path,
    repo_root: Path,
    base_theory_context: str,
    derived_entries: list[dict[str, str]],
    run_id: str,
    run_started_at: str,
    run_started_monotonic: float,
    artifact_paths: dict[str, Path],
    compile_metrics: dict[str, Any],
    worker_settings: Any,
    prover_worker_settings: Any,
    prover_statement_worker_settings: Any,
    formalize_worker_settings: Any,
    repair_worker_settings: Any,
    prioritize_open_problems_worker_settings: Any,
    derived_runtime_state: dict[str, Any],
    record_problem_rows: Callable[..., None],
    record_theorem: Callable[..., None],
) -> None:
    open_path = loop_open_problems_path(data_dir)
    archived_path = loop_archived_problems_path(data_dir)
    state_lock = threading.Lock()
    reserved_problem_ids: set[str] = set()
    problem_futures: dict[concurrent.futures.Future, dict[str, Any]] = {}
    launched_iterations = 0
    completed_problem_sessions = 0
    pending_priority_refresh_ran_for_report = False
    pending_priority_refresh_error_for_report = ""
    stop_requested = False
    interrupt_notice_emitted = False
    iteration_offset = int(getattr(args, "iteration_offset", 0) or 0)

    initial_open_rows = [normalize_open_problem_row(row) for row in read_jsonl(open_path)]
    if needs_bootstrap_priority_refresh(initial_open_rows) or not initial_open_rows:
        bootstrap_iteration = iteration_offset + 1
        emit_phase_log(
            args.phase_logs,
            "open_problem_priority_refresh",
            iteration=bootstrap_iteration,
            tracked_problem_count=len(initial_open_rows) + len(read_archived_problem_rows(data_dir)),
            derived_theorem_count=len(derived_entries),
            reason="bootstrap",
        )
        with state_lock:
            try:
                refresh_result = refresh_open_problem_state(
                    data_dir=data_dir,
                    prioritize_worker_settings=prioritize_open_problems_worker_settings,
                    prioritizer_prompt_file=PRIORITIZE_OPEN_PROBLEMS_PROMPT_FILE,
                    derived_entries=derived_entries,
                    current_iteration=bootstrap_iteration,
                    failure_threshold=args.open_problem_failure_threshold,
                    run_id=run_id,
                    theory_state_history_path=artifact_paths["theory_state_history"],
                    theory_file=Path(THEORY_FILE_PATH),
                    derived_file=derived_path,
                    repo_root=repo_root,
                    batch_generator_seed_count=args.seed_count,
                    batch_generator_open_target_min=BATCH_GENERATOR_OPEN_TARGET_MIN,
                    reserved_problem_ids=reserved_problem_ids,
                    phase_logger=(lambda **fields: emit_phase_log(args.phase_logs, iteration=bootstrap_iteration, **fields)),
                )
                priority_refresh_ran = bool(refresh_result.get("priority_refresh_ran", False))
                priority_refresh_error = str(refresh_result.get("priority_refresh_error", ""))
                priority_refresh_report = dict(refresh_result.get("priority_refresh_report", {}))
            except Exception as exc:
                priority_refresh_ran = False
                priority_refresh_error = str(exc)
                priority_refresh_report = {}
        if priority_refresh_ran:
            record_problem_rows(
                list(priority_refresh_report.get("batch_generator_added_problem_rows", [])),
                iteration=1,
                session_type="batch_generator",
            )
            pending_priority_refresh_ran_for_report = True
            pending_priority_refresh_error_for_report = priority_refresh_error
        elif priority_refresh_error:
            debug_log(f"Initial open problem priority refresh failed: {priority_refresh_error}")
            emit_phase_log(
                args.phase_logs,
                "open_problem_priority_refresh_error",
                iteration=1,
                error=priority_refresh_error,
                reason="bootstrap",
            )
            pending_priority_refresh_error_for_report = priority_refresh_error
    max_workers = max(1, int(args.parallel_sessions))
    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
        while True:
            made_progress = False

            for future, meta in list(problem_futures.items()):
                if not future.done():
                    continue
                made_progress = True
                del problem_futures[future]
                reserved_problem_ids.discard(str(meta.get("problem_id", "")))
                session_result = future.result()
                current_iteration = int(session_result.get("iteration", 0) or 0)
                report = dict(session_result.get("report", {}))
                state_update_report = dict(session_result.get("state_update_report", {}))
                completed_problem_sessions += 1
                if bool(session_result.get("theorem_appended", False)) and str(session_result.get("theorem_name", "")).strip():
                    compile_metrics["solved_per_run"] += 1
                    elapsed_ms = monotonic_duration_ms(run_started_monotonic)
                    if compile_metrics["time_to_first_green_ms"] is None:
                        compile_metrics["time_to_first_green_ms"] = elapsed_ms
                    compile_metrics["wall_clock_to_last_solve_ms"] = elapsed_ms
                    record_theorem(
                        str(session_result.get("theorem_name", "")),
                        str(session_result.get("target_stmt", "")),
                        iteration=current_iteration,
                        session_type="loop",
                    )
                    append_lineage_edge_record(
                        artifact_paths["lineage_edges"],
                        run_id=run_id,
                        iteration=current_iteration,
                        session_type="loop",
                        parent_id=str(session_result.get("problem_id", "")),
                        child_id=str(session_result.get("theorem_name", "")),
                        edge_type="solved_as",
                    )
                added_problem_rows = list(state_update_report.get("added_problem_rows", []))
                record_problem_rows(
                    added_problem_rows,
                    iteration=current_iteration,
                    session_type="loop",
                )
                if bool(report.get("priority_refresh_ran", False)):
                    record_problem_rows(
                        list(report.get("batch_generator_added_problem_rows", [])),
                        iteration=current_iteration,
                        session_type="batch_generator",
                    )
                for added_row in added_problem_rows:
                    added_problem_id = str(added_row.get("id", "")).strip()
                    if added_problem_id:
                        append_lineage_edge_record(
                            artifact_paths["lineage_edges"],
                            run_id=run_id,
                            iteration=current_iteration,
                            session_type="loop",
                            parent_id=str(session_result.get("problem_id", "")),
                            child_id=added_problem_id,
                            edge_type="generated_from",
                        )
                report["priority_refresh_ran"] = bool(
                    report.get("priority_refresh_ran", False) or pending_priority_refresh_ran_for_report
                )
                report["priority_refresh_error"] = str(
                    report.get("priority_refresh_error", "") or pending_priority_refresh_error_for_report
                )
                pending_priority_refresh_ran_for_report = False
                pending_priority_refresh_error_for_report = ""
                print(report)

            with state_lock:
                open_rows = [normalize_open_problem_row(row) for row in read_jsonl(open_path)]
                archived_rows = read_archived_problem_rows(data_dir)
                tracked_rows = open_rows + archived_rows
                if tracked_rows:
                    next_open_rows, newly_archived_rows = split_active_and_archived_problem_queues(
                        open_rows,
                        failure_archive_threshold=args.open_problem_failure_threshold,
                    )
                    next_archived_rows = merge_archived_problem_rows(archived_rows, newly_archived_rows)
                    queue_changed = next_open_rows != open_rows or next_archived_rows != archived_rows
                    open_rows = next_open_rows
                    archived_rows = next_archived_rows
                    if queue_changed:
                        write_jsonl_atomic(open_path, open_rows)
                        write_jsonl_atomic(archived_path, archived_rows)
                derived_entries_snapshot = [dict(entry) for entry in derived_entries]
            can_launch_more_iterations = (
                args.max_iterations is None or launched_iterations < args.max_iterations
            )

            if (
                not stop_requested
                and can_launch_more_iterations
                and (
                    (
                        len(problem_futures) < int(args.parallel_sessions)
                        and not has_available_solver_eligible_problem(
                            open_rows,
                            reserved_problem_ids=reserved_problem_ids,
                        )
                    )
                    or (not tracked_rows and not problem_futures)
                )
            ):
                emit_phase_log(
                    args.phase_logs,
                    "open_problem_priority_refresh",
                    iteration=iteration_offset + launched_iterations + 1,
                    tracked_problem_count=len(tracked_rows),
                    derived_theorem_count=len(derived_entries_snapshot),
                )
                with state_lock:
                    try:
                        refresh_result = refresh_open_problem_state(
                            data_dir=data_dir,
                            prioritize_worker_settings=prioritize_open_problems_worker_settings,
                            prioritizer_prompt_file=PRIORITIZE_OPEN_PROBLEMS_PROMPT_FILE,
                            derived_entries=derived_entries,
                            current_iteration=iteration_offset + launched_iterations + 1,
                            failure_threshold=args.open_problem_failure_threshold,
                            run_id=run_id,
                            theory_state_history_path=artifact_paths["theory_state_history"],
                            theory_file=Path(THEORY_FILE_PATH),
                            derived_file=derived_path,
                            repo_root=repo_root,
                            batch_generator_seed_count=args.seed_count,
                            batch_generator_open_target_min=BATCH_GENERATOR_OPEN_TARGET_MIN,
                            reserved_problem_ids=reserved_problem_ids,
                            phase_logger=(lambda **fields: emit_phase_log(args.phase_logs, iteration=iteration_offset + launched_iterations + 1, **fields)),
                        )
                        priority_refresh_ran = bool(refresh_result.get("priority_refresh_ran", False))
                        priority_refresh_error = str(refresh_result.get("priority_refresh_error", ""))
                        priority_refresh_report = dict(refresh_result.get("priority_refresh_report", {}))
                    except Exception as exc:
                        priority_refresh_ran = False
                        priority_refresh_error = str(exc)
                        priority_refresh_report = {}
                if priority_refresh_ran:
                    record_problem_rows(
                        list(priority_refresh_report.get("batch_generator_added_problem_rows", [])),
                        iteration=launched_iterations + 1,
                        session_type="batch_generator",
                    )
                    pending_priority_refresh_ran_for_report = True
                    pending_priority_refresh_error_for_report = priority_refresh_error
                elif priority_refresh_error:
                    debug_log(f"Open problem priority refresh failed: {priority_refresh_error}")
                    emit_phase_log(
                        args.phase_logs,
                        "open_problem_priority_refresh_error",
                        iteration=iteration_offset + launched_iterations + 1,
                        error=priority_refresh_error,
                    )
                    pending_priority_refresh_error_for_report = priority_refresh_error
                with state_lock:
                    open_rows = [normalize_open_problem_row(row) for row in read_jsonl(open_path)]
                    archived_rows = read_archived_problem_rows(data_dir)
                    tracked_rows = open_rows + archived_rows

            while (
                not stop_requested
                and len(problem_futures) < int(args.parallel_sessions)
                and can_launch_more_iterations
            ):
                picked = pick_next_available_problem(
                    open_rows,
                    reserved_problem_ids=reserved_problem_ids,
                )
                if picked is None:
                    break
                launched_iterations += 1
                current_iteration = iteration_offset + launched_iterations
                problem_id = str(picked.get("id", "")).strip()
                reserved_problem_ids.add(problem_id)
                used_slots = {int(meta.get("slot_index", 0) or 0) for meta in problem_futures.values()}
                slot_index = next(index for index in range(1, int(args.parallel_sessions) + 1) if index not in used_slots)
                future = executor.submit(
                    run_problem_session,
                    args=args,
                    picked=dict(picked),
                    open_rows=[dict(row) for row in open_rows],
                    base_theory_context=base_theory_context,
                    derived_entries_snapshot=[dict(entry) for entry in derived_entries_snapshot],
                    shared_derived_entries=derived_entries,
                    data_dir=data_dir,
                    memory_path=memory_path,
                    derived_path=derived_path,
                    current_iteration=current_iteration,
                    run_id=run_id,
                    artifact_paths=artifact_paths,
                    compile_metrics=compile_metrics,
                    worker_settings=worker_settings,
                    prover_worker_settings=prover_worker_settings,
                    prover_statement_worker_settings=prover_statement_worker_settings,
                    formalize_worker_settings=formalize_worker_settings,
                    repair_worker_settings=repair_worker_settings,
                    prioritize_open_problems_worker_settings=prioritize_open_problems_worker_settings,
                    state_lock=state_lock,
                    derived_runtime_state=derived_runtime_state,
                    scratch_file=build_session_scratch_file(scratch_file, session_type="loop", slot_index=slot_index),
                )
                problem_futures[future] = {
                    "problem_id": problem_id,
                    "slot_index": slot_index,
                }
                made_progress = True

            if stop_requested and not problem_futures:
                finalize_run_summary(
                    artifact_paths["summary"],
                    run_id=run_id,
                    started_at=run_started_at,
                    started_monotonic=run_started_monotonic,
                    metrics=compile_metrics,
                    status="interrupted",
                )
                print(
                    {
                        "status": "interrupted",
                        "iterations_completed": completed_problem_sessions,
                        "priority_refresh_ran": pending_priority_refresh_ran_for_report,
                        "priority_refresh_error": pending_priority_refresh_error_for_report,
                    }
                )
                return

            if args.max_iterations is not None and launched_iterations >= args.max_iterations and not problem_futures:
                finalize_run_summary(
                    artifact_paths["summary"],
                    run_id=run_id,
                    started_at=run_started_at,
                    started_monotonic=run_started_monotonic,
                    metrics=compile_metrics,
                    status="max_iterations_reached",
                )
                print(
                    {
                        "status": "max_iterations_reached",
                        "iterations_completed": completed_problem_sessions,
                        "priority_refresh_ran": pending_priority_refresh_ran_for_report,
                        "priority_refresh_error": pending_priority_refresh_error_for_report,
                    }
                )
                return

            if not tracked_rows and not problem_futures:
                finalize_run_summary(
                    artifact_paths["summary"],
                    run_id=run_id,
                    started_at=run_started_at,
                    started_monotonic=run_started_monotonic,
                    metrics=compile_metrics,
                    status="no_open_problems",
                )
                print(
                    {
                        "status": "no_open_problems",
                        "iterations_completed": completed_problem_sessions,
                        "archived_problem_count": len(archived_rows),
                        "priority_refresh_ran": pending_priority_refresh_ran_for_report,
                        "priority_refresh_error": pending_priority_refresh_error_for_report,
                    }
                )
                return

            if not open_path.exists() and not archived_path.exists() and not problem_futures:
                finalize_run_summary(
                    artifact_paths["summary"],
                    run_id=run_id,
                    started_at=run_started_at,
                    started_monotonic=run_started_monotonic,
                    metrics=compile_metrics,
                    status="open_problems_missing",
                )
                print(
                    {
                        "status": "open_problems_missing",
                        "iterations_completed": completed_problem_sessions,
                        "priority_refresh_ran": pending_priority_refresh_ran_for_report,
                        "priority_refresh_error": pending_priority_refresh_error_for_report,
                    }
                )
                return

            all_futures = list(problem_futures.keys())
            if not made_progress and all_futures:
                try:
                    concurrent.futures.wait(all_futures, return_when=concurrent.futures.FIRST_COMPLETED)
                except KeyboardInterrupt:
                    stop_requested = True
                    if not interrupt_notice_emitted:
                        interrupt_notice_emitted = True
                        debug_log("Interrupt received; stop launching new sessions and drain active work.")
                        print(
                            {
                                "status": "interrupt_requested",
                                "iterations_completed": completed_problem_sessions,
                                "active_problem_sessions": len(problem_futures),
                            }
                        )


def prebuild_lean_project() -> list[dict[str, Any]]:
    """Build Lean artifacts once during initialization.

    Build only the stable library modules here.
    Scratch.lean is a transient verification target and should remain outside
    initialization builds so a broken scratch proof does not block the loop.
    """
    results: list[dict[str, Any]] = []
    for target in (
        "AutomatedTheoryConstruction.Theory",
        "AutomatedTheoryConstruction.Generated.Manifest",
        "AutomatedTheoryConstruction.Derived",
    ):
        started = time.monotonic()
        proc = subprocess.run(
            ["lake", "build", target],
            capture_output=True,
            text=True,
            check=False,
        )
        results.append(
            {
                "target": target,
                "success": proc.returncode == 0,
                "duration_ms": monotonic_duration_ms(started),
                "stderr": proc.stderr,
                "stdout": proc.stdout,
            }
        )
        if proc.returncode != 0:
            stderr = (proc.stderr or "").strip()
            stdout = (proc.stdout or "").strip()
            excerpt = stderr or stdout or f"lake build {target} failed without output"
            raise RuntimeError(f"Initialization build failed for {target}: {excerpt}")
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description="Run the minimal prototype loop.")
    worker_timeout_help = "Per worker subprocess timeout in seconds."
    verify_timeout_help = "Per Lean verification timeout in seconds."
    retry_budget_help = "Whole retry-loop budget in seconds."
    parser.add_argument("--initialize-on-start", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--phase-logs", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--max-iterations", type=int)
    parser.add_argument("--worker-command")
    parser.add_argument("--worker-timeout", type=int, help=worker_timeout_help)
    parser.add_argument("--skip-verify", action="store_true")
    parser.add_argument("--parallel-sessions", type=int, default=1)
    parser.add_argument("--seed-count", type=int, default=BATCH_GENERATOR_SEED_COUNT)
    parser.add_argument("--open-problem-failure-threshold", type=int, default=2)
    parser.add_argument("--prover-retry-budget-sec", type=int, default=DEFAULT_PROVER_RETRY_BUDGET_SEC, help=retry_budget_help)
    parser.add_argument(
        "--formalization-retry-budget-sec",
        type=int,
        default=DEFAULT_FORMALIZATION_RETRY_BUDGET_SEC,
        help=retry_budget_help,
    )
    parser.add_argument("--max-same-error-streak", type=int, default=DEFAULT_MAX_SAME_ERROR_STREAK)
    parser.add_argument("--iteration-offset", type=int, default=0)
    args = parser.parse_args()
    if args.max_iterations is not None and args.max_iterations < 0:
        raise ValueError("--max-iterations must be >= 0")
    if args.open_problem_failure_threshold < 0:
        raise ValueError("--open-problem-failure-threshold must be >= 0")
    if args.parallel_sessions < 1:
        raise ValueError("--parallel-sessions must be >= 1")
    if args.seed_count < 1:
        raise ValueError("--seed-count must be >= 1")
    if args.prover_retry_budget_sec < 0:
        raise ValueError("--prover-retry-budget-sec must be >= 0")
    if args.formalization_retry_budget_sec < 0:
        raise ValueError("--formalization-retry-budget-sec must be >= 0")
    if args.max_same_error_streak < 1:
        raise ValueError("--max-same-error-streak must be >= 1")
    if args.iteration_offset < 0:
        raise ValueError("--iteration-offset must be >= 0")
    data_dir = Path(DATA_DIR_PATH)
    scratch_file = Path(SCRATCH_FILE_PATH)
    memory_path = Path(FORMALIZATION_MEMORY_FILE_PATH)
    archived_problems_path = Path(ARCHIVED_PROBLEMS_FILE_PATH)
    derived_path = Path(DERIVED_FILE_PATH)
    derived_cleanup_files = (
        Path("AutomatedTheoryConstruction/Derived.refactored.preview.lean"),
        Path("AutomatedTheoryConstruction/Derived.refactored.reviewed.lean"),
    )
    run_id = build_run_id("loop")
    run_started_at = iso_timestamp_now()
    run_started_monotonic = time.monotonic()
    artifact_paths = build_run_artifact_paths(data_dir, run_id)
    compile_metrics = {
        "compile_attempt_count": 0,
        "compile_success_count": 0,
        "solved_per_run": 0,
        "time_to_first_green_ms": None,
        "wall_clock_to_last_solve_ms": None,
    }
    recorded_problem_ids: set[str] = set()
    recorded_theorem_names: set[str] = set()
    repo_root = REPO_ROOT
    continuation_snapshot = None
    if not args.initialize_on_start:
        continuation_snapshot = capture_continuation_runtime_snapshot(
            data_dir=data_dir,
            formalization_memory_file=memory_path,
            scratch_file=scratch_file,
            derived_file=derived_path,
            derived_cleanup_files=derived_cleanup_files,
        )

    def record_problem_rows(rows: list[dict[str, Any]], *, iteration: int, session_type: str) -> None:
        for row in rows:
            problem_id = str(row.get("id", "")).strip()
            if not problem_id or problem_id in recorded_problem_ids:
                continue
            append_problem_node_record(
                artifact_paths["problem_nodes"],
                problem_row=row,
                run_id=run_id,
                iteration=iteration,
                session_type=session_type,
            )
            recorded_problem_ids.add(problem_id)

    def record_theorem(theorem_name: str, statement: str, *, iteration: int, session_type: str) -> None:
        normalized_name = theorem_name.strip()
        if not normalized_name or normalized_name in recorded_theorem_names:
            return
        append_theorem_node_record(
            artifact_paths["theorem_nodes"],
            theorem_name=normalized_name,
            statement=statement,
            run_id=run_id,
            iteration=iteration,
            session_type=session_type,
        )
        recorded_theorem_names.add(normalized_name)

    if args.initialize_on_start:
        initialize_runtime_state(
            data_dir=data_dir,
            seeds_file=Path(SEEDS_FILE_PATH),
            scratch_file=scratch_file,
            reset_scratch=RESET_SCRATCH_ON_START,
            derived_file=derived_path,
            derived_cleanup_files=derived_cleanup_files,
            reset_derived=RESET_DERIVED_ON_START,
            formalization_memory_file=memory_path,
            reset_formalization_memory=RESET_FORMALIZATION_MEMORY_ON_START,
            archived_problems_file=archived_problems_path,
        )
        if args.skip_verify:
            debug_log("Skipping initialization lake build because --skip-verify is enabled")
        else:
            debug_log("Running lake build during initialization")
            for build_result in prebuild_lean_project():
                update_compile_metrics(compile_metrics, build_result)
                append_phase_attempt_record(
                    artifact_paths["phase_attempts"],
                    run_id=run_id,
                    session_type="loop",
                    iteration=0,
                    entity_id=str(build_result.get("target", "")),
                    phase="verify",
                    worker_task="initial_lake_build",
                    started_at=run_started_at,
                    finished_at=iso_timestamp_now(),
                    duration_ms=int(build_result.get("duration_ms", 0) or 0),
                    success=bool(build_result.get("success", False)),
                    result="verified" if bool(build_result.get("success", False)) else "failed",
                )
            debug_log("Initialization build completed")
    _, base_theory_context = load_theory_context(Path(THEORY_FILE_PATH))
    derived_entries = extract_derived_theorem_entries(derived_path)
    derived_runtime_state = {
        "generation": load_derived_generation(data_dir),
    }
    persist_derived_generation(
        data_dir,
        generation=int(derived_runtime_state["generation"] or 0),
        run_id=run_id,
        current_iteration=0,
    )
    open_path = loop_open_problems_path(data_dir)
    initial_problem_rows = [normalize_open_problem_row(row) for row in read_jsonl(open_path)]
    initial_problem_rows.extend(read_archived_problem_rows(data_dir))
    record_problem_rows(
        initial_problem_rows,
        iteration=0,
        session_type="loop",
    )

    worker_settings = load_worker_settings(
        command_override=args.worker_command,
        timeout_override=args.worker_timeout,
    )
    prover_worker_settings = load_task_worker_settings(
        task_name="prover",
        base_settings=worker_settings,
    )
    prover_statement_worker_settings = load_task_worker_settings(
        task_name="prover_statement",
        base_settings=worker_settings,
    )
    formalize_worker_settings = load_task_worker_settings(
        task_name="formalize",
        base_settings=worker_settings,
    )
    repair_worker_settings = load_task_worker_settings(
        task_name="repair",
        base_settings=worker_settings,
    )
    prioritize_open_problems_worker_settings = load_task_worker_settings(
        task_name="prioritize_open_problems",
        base_settings=worker_settings,
    )
    try:
        run_parallel_loop(
            args=args,
            data_dir=data_dir,
            scratch_file=scratch_file,
            memory_path=memory_path,
            derived_path=derived_path,
            repo_root=repo_root,
            base_theory_context=base_theory_context,
            derived_entries=derived_entries,
            run_id=run_id,
            run_started_at=run_started_at,
            run_started_monotonic=run_started_monotonic,
            artifact_paths=artifact_paths,
            compile_metrics=compile_metrics,
            worker_settings=worker_settings,
            prover_worker_settings=prover_worker_settings,
            prover_statement_worker_settings=prover_statement_worker_settings,
            formalize_worker_settings=formalize_worker_settings,
            repair_worker_settings=repair_worker_settings,
            prioritize_open_problems_worker_settings=prioritize_open_problems_worker_settings,
            derived_runtime_state=derived_runtime_state,
            record_problem_rows=record_problem_rows,
            record_theorem=record_theorem,
        )
    except Exception:
        guard_against_unexpected_continuation_reset(
            data_dir=data_dir,
            snapshot=continuation_snapshot,
        )
        raise
    guard_against_unexpected_continuation_reset(
        data_dir=data_dir,
        snapshot=continuation_snapshot,
    )
    return


if __name__ == "__main__":
    main()
