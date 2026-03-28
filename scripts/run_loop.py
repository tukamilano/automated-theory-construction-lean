from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
import time
from datetime import datetime
from pathlib import Path
from typing import Callable
from typing import Any

from append_derived import (
    append_theorem,
    build_derived_entries_from_file,
)
from common import (
    ARCHIVED_PROBLEMS_FILENAME,
    LEGACY_DEFERRED_PROBLEMS_FILENAME,
    LEGACY_PRUNED_OPEN_PROBLEMS_FILENAME,
    append_jsonl,
    load_theory_context,
    normalize_open_problem_row,
    normalize_open_problem_priority,
    parse_problem_index,
    partition_open_problem_rows,
    read_archived_problem_rows,
    read_jsonl,
    write_json_atomic,
    write_jsonl_atomic,
)
from import_inference import infer_minimal_imports, render_import_block
from lean_verify import verify_scratch
from state_update import apply_state_update, enqueue_new_problems
from theorem_reuse_memory import append_theorem_reuse_memory_entry
from worker_client import invoke_worker_json, load_task_worker_settings, load_worker_settings


def debug_log(msg: str) -> None:
    """Print debug message to stderr with timestamp."""
    timestamp = time.strftime("%H:%M:%S")
    print(f"[{timestamp}] {msg}", file=sys.stderr, flush=True)



SCRATCH_TEMPLATE = (
    "import Mathlib\n"
    "import AutomatedTheoryConstruction.Theory\n"
    "import AutomatedTheoryConstruction.Derived\n\n"
    "set_option autoImplicit false\n\n"
    "namespace AutomatedTheoryConstruction\n\n"
    "-- Temporary Lean code generated for verification is written here.\n\n"
    "end AutomatedTheoryConstruction\n"
)

DERIVED_TEMPLATE = (
    "import Mathlib\n"
    "import AutomatedTheoryConstruction.Theory\n\n"
    "set_option autoImplicit false\n\n"
    "namespace AutomatedTheoryConstruction\n\n"
    "-- Verified theorems are appended here by scripts/append_derived.py.\n"
    "-- Keep any short theorem docstrings/comments here instead of a separate metadata index.\n\n"
    "end AutomatedTheoryConstruction\n"
)

THEOREM_NAME_STEM_PATTERN = re.compile(r"^[a-z][a-z0-9_]*$")
THEOREM_NAME_PATTERN = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
DERIVED_THEOREM_HEADER_PATTERN = re.compile(r"\btheorem\s+([A-Za-z0-9_']+)\s*:\s*(.+?)\s*:=", re.DOTALL)
UNUSED_VARIABLE_WARNING_PATTERN = re.compile(r"unused variable\s+`([^`]+)`", re.IGNORECASE)
OPEN_PROBLEM_PRIORITY_ORDER = {
    "high": 0,
    "medium": 1,
    "unknown": 2,
    "low": 3,
}


def iso_timestamp_now() -> str:
    return datetime.now().astimezone().isoformat(timespec="seconds")


def monotonic_duration_ms(started_at: float) -> int:
    return int((time.monotonic() - started_at) * 1000)


def build_run_id(kind: str = "loop") -> str:
    return f"{time.strftime('%Y%m%d-%H%M%S')}-{kind}"


def build_run_artifact_paths(data_dir: Path, run_id: str) -> dict[str, Path]:
    run_dir = data_dir / "runs" / run_id
    return {
        "run_dir": run_dir,
        "summary": run_dir / "summary.json",
        "phase_attempts": run_dir / "phase_attempts.jsonl",
        "problem_nodes": run_dir / "problem_nodes.jsonl",
        "theorem_nodes": run_dir / "theorem_nodes.jsonl",
        "lineage_edges": run_dir / "lineage_edges.jsonl",
    }


def append_phase_attempt_record(
    phase_attempts_path: Path,
    *,
    run_id: str,
    session_type: str,
    iteration: int,
    entity_id: str,
    phase: str,
    worker_task: str,
    started_at: str,
    finished_at: str,
    duration_ms: int,
    success: bool,
    result: str,
    timeout: bool = False,
    error: str = "",
) -> None:
    append_jsonl(
        phase_attempts_path,
        {
            "run_id": run_id,
            "session_type": session_type,
            "iteration": iteration,
            "entity_id": entity_id,
            "phase": phase,
            "worker_task": worker_task,
            "started_at": started_at,
            "finished_at": finished_at,
            "duration_ms": duration_ms,
            "success": bool(success),
            "result": result,
            "timeout": bool(timeout),
            "error": error,
        },
    )


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


def normalize_stmt_text(stmt: str) -> str:
    return " ".join(stmt.split())


def open_problem_priority_label(row: dict[str, Any]) -> str:
    return normalize_open_problem_priority(row.get("priority"))


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


def should_refresh_open_problem_priorities(
    open_rows: list[dict[str, Any]],
    *,
    derived_theorem_count: int,
    last_refresh_theorem_count: int,
    refresh_interval: int,
) -> bool:
    if last_refresh_theorem_count == 0 and any(open_problem_priority_label(row) == "unknown" for row in open_rows):
        return True
    if refresh_interval <= 0:
        return False
    return derived_theorem_count - last_refresh_theorem_count >= refresh_interval


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


def is_trivial_negation_style(stmt: str) -> bool:
    normalized = normalize_stmt_text(stmt)
    return normalized.startswith("¬(") or normalized.endswith("→ False")


def pick_next_problem(open_rows: list[dict[str, Any]]) -> dict[str, Any] | None:
    return open_rows[0] if open_rows else None


def validate_prover_output(payload: dict[str, Any], expected_problem_id: str) -> tuple[str, str, str, list[str]]:
    required_keys = {"problem_id", "result", "proof_sketch", "counterexample_text", "new_problems"}
    if set(payload.keys()) != required_keys:
        raise ValueError("prover output keys mismatch required contract")

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

    new_problems_value = payload.get("new_problems")
    if not isinstance(new_problems_value, list):
        raise ValueError("new_problems must be an array of strings")
    if len(new_problems_value) > 2:
        raise ValueError("new_problems must have length <= 2")
    if any((not isinstance(item, str)) for item in new_problems_value):
        raise ValueError("new_problems must contain only strings")

    new_problems = []
    return result, proof_sketch, counterexample_text, new_problems


def validate_theorem_name_stem(stem: str) -> str:
    cleaned = stem.strip()
    if not cleaned:
        raise ValueError("prover_statement theorem_name_stem must be non-empty when result=ok")
    if len(cleaned) > 80:
        raise ValueError("prover_statement theorem_name_stem must be <= 80 characters")
    if not THEOREM_NAME_STEM_PATTERN.fullmatch(cleaned):
        raise ValueError(
            "prover_statement theorem_name_stem must match ^[a-z][a-z0-9_]*$"
        )
    if cleaned.startswith("thm_") or cleaned == "thm":
        raise ValueError("prover_statement theorem_name_stem must not include the thm prefix")
    if cleaned.startswith("_") or cleaned.endswith("_") or "__" in cleaned:
        raise ValueError("prover_statement theorem_name_stem must not have leading/trailing/repeated underscores")
    if re.search(r"_\d+$", cleaned):
        raise ValueError("prover_statement theorem_name_stem must not end with a numeric suffix")
    return cleaned


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


def validate_prover_statement_output(payload: dict[str, Any], expected_problem_id: str) -> tuple[str, str, str, str, str]:
    required_keys = {"problem_id", "result", "lean_statement", "theorem_name_stem", "docstring_summary", "notes"}
    if set(payload.keys()) != required_keys:
        raise ValueError(
            "prover_statement output must contain exactly: problem_id, result, lean_statement, theorem_name_stem, docstring_summary, notes"
        )

    problem_id = payload.get("problem_id")
    if problem_id != expected_problem_id:
        raise ValueError("prover_statement output problem_id does not match picked problem")

    result = payload.get("result")
    if result not in {"ok", "stuck"}:
        raise ValueError("prover_statement result must be one of: ok, stuck")

    lean_statement = payload.get("lean_statement")
    theorem_name_stem = payload.get("theorem_name_stem")
    docstring_summary = payload.get("docstring_summary")
    notes = payload.get("notes")
    if not isinstance(lean_statement, str) or not isinstance(theorem_name_stem, str) or not isinstance(docstring_summary, str) or not isinstance(notes, str):
        raise ValueError("prover_statement lean_statement, theorem_name_stem, docstring_summary, and notes must be strings")
    if result == "ok" and not lean_statement.strip():
        raise ValueError("prover_statement lean_statement must be non-empty when result=ok")
    if result == "ok":
        theorem_name_stem = validate_theorem_name_stem(theorem_name_stem)
    else:
        theorem_name_stem = theorem_name_stem.strip()
        if theorem_name_stem:
            raise ValueError("prover_statement theorem_name_stem must be empty when result=stuck")
        docstring_summary = docstring_summary.strip()
        if docstring_summary:
            raise ValueError("prover_statement docstring_summary must be empty when result=stuck")

    return result, lean_statement.strip(), theorem_name_stem, docstring_summary.strip(), notes.strip()


def validate_formalizer_output(payload: dict[str, Any], expected_problem_id: str) -> tuple[str, str, str, str]:
    required_keys = {"problem_id", "result", "proof_sketch", "proof_text", "counterexample_text"}
    if set(payload.keys()) != required_keys:
        raise ValueError("formalizer output keys mismatch required contract")

    problem_id = payload.get("problem_id")
    if problem_id != expected_problem_id:
        raise ValueError("formalizer output problem_id does not match picked problem")

    result = payload.get("result")
    if result not in {"proof", "counterexample", "stuck"}:
        raise ValueError("formalizer result must be one of: proof, counterexample, stuck")

    proof_sketch = payload.get("proof_sketch")
    proof_text = payload.get("proof_text")
    counterexample_text = payload.get("counterexample_text")
    if not isinstance(proof_sketch, str) or not isinstance(proof_text, str) or not isinstance(counterexample_text, str):
        raise ValueError("formalizer proof_sketch, proof_text and counterexample_text must be strings")

    return result, proof_sketch, proof_text, counterexample_text


def validate_expand_output(payload: dict[str, Any], expected_problem_id: str) -> list[dict[str, str]]:
    required_keys = {"problem_id", "candidates"}
    if set(payload.keys()) != required_keys:
        raise ValueError("expand output must contain exactly: problem_id, candidates")

    problem_id = payload.get("problem_id")
    if problem_id != expected_problem_id:
        raise ValueError("expand output problem_id does not match picked problem")

    candidates_value = payload.get("candidates")
    if not isinstance(candidates_value, list):
        raise ValueError("expand candidates must be an array of objects")
    if len(candidates_value) > 2:
        raise ValueError("expand candidates must have length <= 2")

    parsed: list[dict[str, str]] = []
    seen_norms: set[str] = set()
    for item in candidates_value:
        if not isinstance(item, dict) or set(item.keys()) != {"statement", "rationale"}:
            raise ValueError("each expand candidate must contain exactly: statement, rationale")
        statement = item.get("statement")
        rationale = item.get("rationale")
        if not isinstance(statement, str) or not isinstance(rationale, str):
            raise ValueError("expand candidate statement and rationale must be strings")
        normalized_statement = statement.strip()
        if not normalized_statement:
            continue
        norm = normalize_stmt_text(normalized_statement)
        if norm in seen_norms:
            continue
        seen_norms.add(norm)
        parsed.append({"statement": normalized_statement, "rationale": rationale.strip()})

    return parsed[:2]


def validate_problem_candidates_output(
    payload: dict[str, Any],
    *,
    expected_problem_id: str,
    max_candidates: int,
) -> list[dict[str, str]]:
    required_keys = {"problem_id", "candidates"}
    if set(payload.keys()) != required_keys:
        raise ValueError("candidate output must contain exactly: problem_id, candidates")

    problem_id = payload.get("problem_id")
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
        norm = normalize_stmt_text(normalized_statement)
        if norm in seen_norms:
            continue
        seen_norms.add(norm)
        parsed.append({"statement": normalized_statement, "rationale": rationale.strip()})

    return parsed[:max_candidates]


def validate_open_problem_priority_output(
    payload: dict[str, Any],
    expected_problem_ids: list[str],
) -> list[dict[str, str]]:
    required_keys = {"priorities"}
    if set(payload.keys()) != required_keys:
        raise ValueError("priority refresh output must contain exactly: priorities")

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

    return parsed


def validate_main_theorem_suggestion_output(
    payload: dict[str, Any],
    expected_candidate_id: str,
) -> tuple[str, str, str, str, str, list[str], list[str]]:
    required_keys = {
        "candidate_id",
        "result",
        "statement",
        "theorem_name_stem",
        "docstring_summary",
        "rationale",
        "supporting_theorems",
        "missing_lemmas",
    }
    if set(payload.keys()) != required_keys:
        raise ValueError("main_theorem_suggest output keys mismatch required contract")

    candidate_id = str(payload.get("candidate_id", "")).strip()
    if candidate_id != expected_candidate_id:
        raise ValueError("main_theorem_suggest candidate_id does not match request")

    result = str(payload.get("result", "")).strip()
    if result not in {"ok", "stuck"}:
        raise ValueError("main_theorem_suggest result must be ok|stuck")

    statement = str(payload.get("statement", "")).strip()
    theorem_name_stem = str(payload.get("theorem_name_stem", "")).strip()
    docstring_summary = str(payload.get("docstring_summary", "")).strip()
    rationale = str(payload.get("rationale", "")).strip()
    supporting = payload.get("supporting_theorems", [])
    missing = payload.get("missing_lemmas", [])
    if not isinstance(supporting, list) or not isinstance(missing, list):
        raise ValueError("main_theorem_suggest supporting_theorems and missing_lemmas must be arrays")

    supporting_theorems = [str(item).strip() for item in supporting if str(item).strip()]
    missing_lemmas = [str(item).strip() for item in missing if str(item).strip()]

    if result == "ok":
        if not statement:
            raise ValueError("main_theorem_suggest statement must be non-empty when result=ok")
        theorem_name_stem = validate_theorem_name_stem(theorem_name_stem)
        if not docstring_summary:
            raise ValueError("main_theorem_suggest docstring_summary must be non-empty when result=ok")
    else:
        if statement or theorem_name_stem or docstring_summary:
            raise ValueError("main_theorem_suggest stuck result must not return statement/name/docstring")

    return (
        result,
        statement,
        theorem_name_stem,
        docstring_summary,
        rationale,
        supporting_theorems,
        missing_lemmas,
    )


def validate_main_theorem_plan_output(
    payload: dict[str, Any],
    expected_candidate_id: str,
) -> tuple[str, str, str, list[str], list[str], str]:
    required_keys = {
        "candidate_id",
        "result",
        "plan_summary",
        "proof_sketch",
        "supporting_theorems",
        "intermediate_lemmas",
        "notes",
    }
    if set(payload.keys()) != required_keys:
        raise ValueError("main_theorem_plan output keys mismatch required contract")

    candidate_id = str(payload.get("candidate_id", "")).strip()
    if candidate_id != expected_candidate_id:
        raise ValueError("main_theorem_plan candidate_id does not match request")

    result = str(payload.get("result", "")).strip()
    if result not in {"ok", "stuck"}:
        raise ValueError("main_theorem_plan result must be ok|stuck")

    plan_summary = str(payload.get("plan_summary", "")).strip()
    proof_sketch = str(payload.get("proof_sketch", "")).strip()
    notes = str(payload.get("notes", "")).strip()
    supporting = payload.get("supporting_theorems", [])
    intermediate = payload.get("intermediate_lemmas", [])
    if not isinstance(supporting, list) or not isinstance(intermediate, list):
        raise ValueError("main_theorem_plan supporting_theorems and intermediate_lemmas must be arrays")

    supporting_theorems = [str(item).strip() for item in supporting if str(item).strip()]
    intermediate_lemmas = [str(item).strip() for item in intermediate if str(item).strip()]
    if result == "ok" and not proof_sketch:
        raise ValueError("main_theorem_plan proof_sketch must be non-empty when result=ok")
    return result, plan_summary, proof_sketch, supporting_theorems, intermediate_lemmas, notes


def load_prompt_text(prompt_file: str) -> str:
    path = Path(prompt_file)
    if not path.exists():
        raise ValueError(f"Prompt file not found: {prompt_file}")
    return path.read_text(encoding="utf-8")


def formalize_to_scratch(
    theorem_name: str,
    stmt: str,
    mode: str,
    proof_text: str,
    counterexample_text: str,
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

    scratch = (
        render_import_block(extra_imports)
        + 
        "import AutomatedTheoryConstruction.Theory\n"
        "import AutomatedTheoryConstruction.Derived\n\n"
        "set_option autoImplicit false\n\n"
        "namespace AutomatedTheoryConstruction\n\n"
        f"{theorem}\n"
        "end AutomatedTheoryConstruction\n"
    )
    return theorem_name, scratch


def validate_solver_statement_with_lean(
    *,
    problem_id: str,
    theorem_name: str,
    stmt: str,
    timeout_sec: int = 180,
) -> dict[str, Any]:
    _, scratch = formalize_to_scratch(
        theorem_name=theorem_name,
        stmt=stmt,
        mode="proof",
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
        return verify_scratch(problem_id, "proof", temp_path, timeout_sec=timeout_sec)
    finally:
        if temp_path is not None:
            temp_path.unlink(missing_ok=True)


def parse_new_problems(raw_values: list[str]) -> list[str]:
    values: list[str] = []
    for raw in raw_values:
        text = raw.strip()
        if text:
            values.append(text)
    return values[:2]


def merge_new_problems(existing: list[str], incoming: list[str], *, max_items: int = 2) -> list[str]:
    """Merge and deduplicate generated problems while keeping order and cap."""
    merged: list[str] = []
    seen: set[str] = set()

    for item in list(existing) + list(incoming):
        text = str(item).strip()
        if not text:
            continue
        norm = normalize_stmt_text(text)
        if norm in seen:
            continue
        seen.add(norm)
        merged.append(text)
        if len(merged) >= max_items:
            break

    return merged[:max_items]


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


def emit_phase_log(enabled: bool, phase: str, **fields: Any) -> None:
    if not enabled:
        return
    payload: dict[str, Any] = {
        "event": "phase",
        "phase": phase,
        "ts": int(time.time()),
    }
    payload.update(fields)
    print(payload, flush=True)


def emit_parse_phase_log(enabled: bool, phase: str, *, iteration: int, problem_id: str, worker_meta: dict[str, Any]) -> None:
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
    if worker_fallback or client_fallback:
        payload["fallback_used"] = worker_fallback or client_fallback
    emit_phase_log(enabled, phase, **payload)


def is_worker_timeout_error(exc: Exception) -> bool:
    message = str(exc).lower()
    return "timed out" in message or "timeout" in message


def filter_generated_subgoals(candidates: list[str], original_stmt: str) -> list[str]:
    """Keep only meaningful, non-trivial generated subgoals.

    Rejects direct logical-negation templates and duplicates to reduce queue pollution.
    """
    original_norm = normalize_stmt_text(original_stmt)
    filtered: list[str] = []
    seen_norms: set[str] = set()

    for candidate in candidates:
        text = str(candidate).strip()
        if not text:
            continue

        norm = normalize_stmt_text(text)
        if norm == original_norm:
            continue

        # Avoid mechanical timeout templates such as ¬(P) and P → False.
        if is_trivial_negation_style(norm):
            continue

        if norm in seen_norms:
            continue
        seen_norms.add(norm)
        filtered.append(text)

    return filtered[:2]


def collect_recent_subgoal_candidates(
    memory_path: Path,
    problem_id: str,
    max_candidates: int = 16,
) -> list[str]:
    """Collect candidate subgoals from same-problem formalization memory only."""
    if not memory_path.exists():
        return []

    try:
        payload = json.loads(memory_path.read_text(encoding="utf-8"))
    except Exception:
        return []

    if not isinstance(payload, dict):
        return []

    candidates: list[str] = []

    def add_from_rows(rows: Any) -> None:
        if not isinstance(rows, list):
            return
        # Prefer latest rows first.
        for item in reversed(rows):
            if not isinstance(item, dict):
                continue
            row_candidates = item.get("new_problems", [])
            if not isinstance(row_candidates, list):
                continue
            for row_candidate in row_candidates:
                if isinstance(row_candidate, str) and row_candidate.strip():
                    candidates.append(row_candidate.strip())
                    if len(candidates) >= max_candidates:
                        return

    # Use only same-problem history to respect proof-local reasoning context.
    add_from_rows(payload.get(problem_id, []))
    return candidates[:max_candidates]


def make_timeout_subgoals(
    stmt: str,
    memory_path: Path,
    problem_id: str,
    fallback_candidates: list[str] | None = None,
) -> list[str]:
    """Generate follow-up subgoals from prior unresolved reasoning history.

    Uses prior repair/prover proposals from formalization memory and avoids synthetic
    logical-negation templates.
    """
    candidates = collect_recent_subgoal_candidates(memory_path, problem_id)

    if fallback_candidates:
        candidates.extend(fallback_candidates)

    return filter_generated_subgoals(candidates, stmt)


def extract_derived_theorem_entries(
    derived_path: Path,
    max_theorems: int | None = None,
) -> list[dict[str, str]]:
    """Extract theorem entries directly from Derived.lean."""
    fallback_entries = build_derived_entries_from_file(derived_path, max_theorems=max_theorems)
    return [
        {
            "name": str(entry.get("theorem_name", "")).strip(),
            "statement": str(entry.get("statement", "")).strip(),
        }
        for entry in fallback_entries[:max_theorems]
        if str(entry.get("theorem_name", "")).strip() and str(entry.get("statement", "")).strip()
    ]


def extract_derived_entry_from_theorem_code(theorem_code: str) -> dict[str, str] | None:
    match = DERIVED_THEOREM_HEADER_PATTERN.search(theorem_code)
    if match is None:
        return None

    theorem_name = str(match.group(1)).strip()
    statement = normalize_stmt_text(str(match.group(2)).strip())
    if not theorem_name or not statement:
        return None

    return {
        "name": theorem_name,
        "statement": statement,
    }


def append_derived_entry_cache(
    entries: list[dict[str, str]],
    theorem_code: str,
) -> None:
    entry = extract_derived_entry_from_theorem_code(theorem_code)
    if entry is None:
        return
    if any(existing["name"] == entry["name"] for existing in entries):
        return
    entries.append(entry)


def extract_theorem_code_from_scratch(scratch_path: Path) -> str:
    scratch_code = scratch_path.read_text(encoding="utf-8")
    theorem_body_match = re.search(
        r"namespace AutomatedTheoryConstruction\n\n(.*)\nend AutomatedTheoryConstruction",
        scratch_code,
        re.DOTALL,
    )
    if theorem_body_match is None:
        return ""
    return theorem_body_match.group(1).strip()


def append_verified_theorem_from_scratch(
    *,
    scratch_path: Path,
    derived_file: Path,
    derived_entries: list[dict[str, str]],
    docstring: str,
) -> str:
    theorem_code = extract_theorem_code_from_scratch(scratch_path)
    if not theorem_code:
        return ""
    appended = append_theorem(
        derived_file,
        theorem_code,
        None,
        docstring,
    )
    if appended:
        append_derived_entry_cache(derived_entries, theorem_code)
    return theorem_code


def classify_statement_shape(stmt: str) -> dict[str, bool]:
    normalized = normalize_stmt_text(stmt)
    return {
        "has_forall": "∀" in normalized,
        "has_exists": "∃" in normalized,
        "has_negation": "¬" in normalized,
        "has_mul": "*" in normalized,
        "has_eq": "=" in normalized,
        "has_subsingleton": "Subsingleton" in normalized,
    }


def extract_relevance_keywords(stmt: str) -> set[str]:
    words = re.findall(r"[A-Za-z_][A-Za-z0-9_']*", stmt)
    stopwords = {
        "Type",
        "SemigroupLike01",
        "Mul",
        "op",
        "x",
        "y",
        "z",
        "h",
        "by",
        "fun",
        "let",
        "intro",
        "have",
        "show",
    }
    keywords = {word for word in words if len(word) >= 4 and word not in stopwords}
    if "Subsingleton" in stmt:
        keywords.add("Subsingleton")
    return keywords


def extract_entry_relevance_keywords(entry: dict[str, Any]) -> set[str]:
    keywords = set(extract_relevance_keywords(str(entry.get("statement", ""))))
    keywords |= extract_relevance_keywords(str(entry.get("name", "")).replace("_", " "))
    return keywords


def same_relevance_family(target_shape: dict[str, bool], entry_shape: dict[str, bool]) -> bool:
    return (
        target_shape["has_forall"] == entry_shape["has_forall"]
        and target_shape["has_exists"] == entry_shape["has_exists"]
        and target_shape["has_negation"] == entry_shape["has_negation"]
        and target_shape["has_mul"] == entry_shape["has_mul"]
        and target_shape["has_eq"] == entry_shape["has_eq"]
        and target_shape["has_subsingleton"] == entry_shape["has_subsingleton"]
    )


def summarize_derived_statement(statement: str, max_chars: int = 120) -> str:
    text = normalize_stmt_text(statement)
    semigroup_prefix = "∀ {α : Type u} [SemigroupLike01 α], "
    if text.startswith(semigroup_prefix):
        text = text[len(semigroup_prefix) :]
    if len(text) > max_chars:
        return text[: max_chars - 3] + "..."
    return text


def shortlist_relevant_derived_entries(
    entries: list[dict[str, Any]],
    stmt: str,
    max_entries: int = 5,
) -> list[dict[str, Any]]:
    if not entries:
        return []

    target_norm = normalize_stmt_text(stmt)
    target_shape = classify_statement_shape(stmt)
    target_keywords = extract_relevance_keywords(stmt)
    shortlisted: list[dict[str, Any]] = []
    seen_names: set[str] = set()

    def add_pass(predicate: Callable[[dict[str, Any]], bool]) -> None:
        for entry in entries:
            if entry["name"] in seen_names:
                continue
            if normalize_stmt_text(entry["statement"]) == target_norm:
                continue
            if not predicate(entry):
                continue
            shortlisted.append(entry)
            seen_names.add(entry["name"])
            if len(shortlisted) >= max_entries:
                return

    def entry_shape(entry: dict[str, Any]) -> dict[str, bool]:
        return classify_statement_shape(entry["statement"])

    add_pass(
        lambda entry: same_relevance_family(target_shape, entry_shape(entry))
        and bool(target_keywords & extract_entry_relevance_keywords(entry))
    )
    add_pass(lambda entry: same_relevance_family(target_shape, entry_shape(entry)))
    add_pass(
        lambda entry: target_shape["has_exists"] == entry_shape(entry)["has_exists"]
        and target_shape["has_negation"] == entry_shape(entry)["has_negation"]
        and target_shape["has_mul"] == entry_shape(entry)["has_mul"]
    )
    return shortlisted[:max_entries]


def render_relevant_derived_context(entries: list[dict[str, Any]], max_chars: int = 1800) -> str:
    if not entries:
        return ""

    lines = [
        "",
        "-- Relevant verified theorems from Derived.lean:",
        "-- Check these theorem names before re-deriving from axioms.",
    ]
    for entry in entries:
        lines.append(f"-- {entry['name']} :: {summarize_derived_statement(entry['statement'])}")

    summary = "\n".join(lines)
    if len(summary) > max_chars:
        summary = summary[:max_chars] + "\n-- (relevant theorem list truncated)"
    return summary


def infer_mathlib_search_terms(stmt: str, entries: list[dict[str, Any]], max_terms: int = 10) -> list[str]:
    target_shape = classify_statement_shape(stmt)
    terms: list[str] = []

    def add(term: str) -> None:
        cleaned = term.strip()
        if not cleaned or cleaned in terms:
            return
        terms.append(cleaned)

    for keyword in sorted(extract_relevance_keywords(stmt)):
        add(keyword)

    if target_shape["has_subsingleton"]:
        add("Subsingleton")
        add("Subsingleton.elim")
    if target_shape["has_exists"]:
        add("Exists")
        add("Classical.choose")
    if target_shape["has_negation"]:
        add("False")
        add("by_contra")
    if target_shape["has_mul"]:
        add("mul")
    if target_shape["has_eq"]:
        add("Eq")
    if target_shape["has_forall"]:
        add("forall")
    for entry in entries:
        add(str(entry.get("name", "")))

    return terms[:max_terms]


def infer_tactic_hints(stmt: str, entries: list[dict[str, Any]], max_tactics: int = 8) -> list[str]:
    target_shape = classify_statement_shape(stmt)
    tactics: list[str] = []

    def add(tactic: str) -> None:
        cleaned = tactic.strip()
        if not cleaned or cleaned in tactics:
            return
        tactics.append(cleaned)

    for tactic in ["simpa", "exact", "rw", "apply", "have", "calc"]:
        add(tactic)

    if target_shape["has_forall"]:
        add("intro")
    if target_shape["has_exists"]:
        add("refine")
        add("constructor")
        add("use")
        add("rcases")
    if target_shape["has_negation"]:
        add("intro")
        add("exfalso")
    if target_shape["has_subsingleton"]:
        add("Subsingleton.elim")
    if target_shape["has_eq"] and target_shape["has_mul"]:
        add("simp only")
    for entry in entries:
        if entry.get("name"):
            add(f"simpa using {entry['name']}")

    for tactic in ["aesop", "grind", "omega", "linarith", "nlinarith", "ring_nf", "positivity"]:
        add(tactic)

    return tactics[:max_tactics]


def render_mathlib_hint_context(stmt: str, entries: list[dict[str, Any]], max_chars: int = 900) -> str:
    search_terms = infer_mathlib_search_terms(stmt, entries)
    tactic_hints = infer_tactic_hints(stmt, entries)
    if not search_terms and not tactic_hints:
        return ""

    lines = [
        "",
        "-- Mathlib reuse hints:",
    ]
    if search_terms:
        lines.append(f"-- search keywords: {', '.join(search_terms)}")
    if tactic_hints:
        lines.append(f"-- tactic candidates: {', '.join(tactic_hints)}")
    lines.append("-- Prefer a short proof using existing Mathlib or Derived facts over axiom-only reconstruction.")

    summary = "\n".join(lines)
    if len(summary) > max_chars:
        summary = summary[:max_chars] + "\n-- (mathlib hints truncated)"
    return summary


def build_problem_theory_context(
    theory_context: str,
    derived_entries: list[dict[str, str]],
    stmt: str,
) -> str:
    relevant_entries = shortlist_relevant_derived_entries(derived_entries, stmt)
    relevant_summary = render_relevant_derived_context(relevant_entries)
    mathlib_summary = render_mathlib_hint_context(stmt, relevant_entries)
    context = theory_context
    if relevant_summary:
        context += relevant_summary
    if mathlib_summary:
        context += mathlib_summary
    return context


def analyze_lean_failure(stderr: str, stdout: str) -> dict[str, Any]:
    text = (stderr or "") + "\n" + (stdout or "")
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    top_lines = lines[:12]
    categories: list[str] = []

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
    if not categories:
        categories.append("other")

    fingerprint = " | ".join(top_lines[:3]) if top_lines else "no_diagnostics"
    return {
        "fingerprint": fingerprint,
        "categories": categories,
        "top_lines": top_lines,
    }


def file_contains_sorry(path: Path) -> bool:
    try:
        content = path.read_text(encoding="utf-8")
    except Exception:
        return False
    return bool(re.search(r"\bsorry\b", content))


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


def load_formalization_memory(memory_path: Path, problem_id: str) -> list[dict[str, Any]]:
    if not memory_path.exists():
        return []
    try:
        payload = json.loads(memory_path.read_text(encoding="utf-8"))
    except Exception:
        return []
    if not isinstance(payload, dict):
        return []
    rows = payload.get(problem_id, [])
    if not isinstance(rows, list):
        return []
    safe_rows: list[dict[str, Any]] = []
    for item in rows:
        if not isinstance(item, dict):
            continue
        raw_new_problems = item.get("new_problems", [])
        parsed_new_problems: list[str] = []
        if isinstance(raw_new_problems, list):
            parsed_new_problems = [str(v).strip() for v in raw_new_problems if str(v).strip()]
        safe_rows.append(
            {
                "stage": str(item.get("stage", "")),
                "source_statement": str(item.get("source_statement", "")),
                "formalized_statement": str(item.get("formalized_statement", "")),
                "statement_formalization_notes": str(item.get("statement_formalization_notes", "")),
                "result": str(item.get("result", "")),
                "verify_success": bool(item.get("verify_success", False)),
                "proof_sketch": str(item.get("proof_sketch", "")),
                "proof_text": str(item.get("proof_text", "")),
                "counterexample_text": str(item.get("counterexample_text", "")),
                "lean_error_excerpt": str(item.get("lean_error_excerpt", "")),
                "lean_error_fingerprint": str(item.get("lean_error_fingerprint", "")),
                "new_problems": parsed_new_problems[:2],
            }
        )
    return safe_rows


def save_formalization_memory(memory_path: Path, problem_id: str, history: list[dict[str, Any]]) -> None:
    memory_path.parent.mkdir(parents=True, exist_ok=True)
    payload: dict[str, Any] = {}
    if memory_path.exists():
        try:
            existing = json.loads(memory_path.read_text(encoding="utf-8"))
            if isinstance(existing, dict):
                payload = existing
        except Exception:
            payload = {}
    payload[problem_id] = history[-20:]
    memory_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")


def append_formalization_memory_entry(
    memory_path: Path,
    problem_id: str,
    entry: dict[str, Any],
) -> list[dict[str, Any]]:
    history = load_formalization_memory(memory_path, problem_id)
    history.append(entry)
    if len(history) > 20:
        history = history[-20:]
    save_formalization_memory(memory_path, problem_id, history)
    return history


def query_prover_with_retries(
    worker_settings: Any,
    prover_prompt: str,
    problem_id: str,
    stmt: str,
    original_stmt: str,
    open_rows: list[dict[str, Any]],
    prover_retries: int,
    theory_context: str,
    memory_path: Path,
    current_iteration_full_logs: list[dict[str, Any]],
    same_problem_history_tail: list[dict[str, Any]],
    run_id: str,
    session_type: str,
    iteration: int,
    phase_attempts_path: Path,
) -> tuple[str, str, str, list[str], int, dict[str, Any]]:
    retries = max(1, prover_retries)
    last_result = "stuck"
    last_proof_sketch = ""
    last_counterexample_text = ""
    last_new_problems: list[str] = []
    last_worker_meta: dict[str, Any] = {}

    for attempt in range(1, retries + 1):
        payload: dict[str, Any] = {
            "problem_id": problem_id,
            "stmt": stmt,
            "original_stmt": original_stmt,
            "theory_context": theory_context,
            "same_problem_history_tail": same_problem_history_tail,
        }
        if attempt > 1:
            payload["retry_instruction"] = (
                "Previous attempt returned stuck. Try a different angle. "
                "If you still cannot prove or refute, return at least one concrete "
                "counterexample candidate in counterexample_text."
            )
            payload["previous_result"] = last_result
            payload["previous_proof_sketch"] = last_proof_sketch
            payload["previous_counterexample_text"] = last_counterexample_text
            payload["previous_new_problems"] = last_new_problems

        try:
            debug_log(f"Calling prover for problem {problem_id}, attempt {attempt}/{retries}")
            prover_started_monotonic = time.monotonic()
            prover_started_at = iso_timestamp_now()
            prover_payload, worker_meta = invoke_worker_json(
                settings=worker_settings,
                task_type="prover",
                system_prompt=prover_prompt,
                payload=payload,
                metadata={"problem_id": problem_id, "attempt": attempt},
            )
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
                timeout_subgoals = make_timeout_subgoals(
                    stmt=stmt,
                    memory_path=memory_path,
                    problem_id=problem_id,
                    fallback_candidates=last_new_problems,
                )
                return "stuck", timeout_sketch, "", timeout_subgoals, attempt, last_worker_meta
            raise
        result, proof_sketch, counterexample_text, new_problems = validate_prover_output(prover_payload, problem_id)
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

        last_result = result
        last_proof_sketch = proof_sketch
        last_counterexample_text = counterexample_text
        last_new_problems = new_problems

        if result != "stuck":
            return result, proof_sketch, counterexample_text, new_problems, attempt, last_worker_meta

    return (
        last_result,
        last_proof_sketch,
        last_counterexample_text,
        last_new_problems,
        retries,
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
) -> tuple[str, str, str, str]:
    formalize_payload: dict[str, Any] = {
        "problem_id": problem_id,
        "stmt": stmt,
        "result": result,
        "proof_sketch": proof_sketch,
        "counterexample_text": counterexample_text,
        "theory_context": theory_context,
        "open_problems": open_rows,
        "same_problem_history_tail": same_problem_history_tail,
        "mathlib_allowed": True,
    }
    formalized, formalize_worker_meta = invoke_worker_json(
        settings=formalize_worker_settings,
        task_type="formalize",
        system_prompt=formalizer_prompt,
        payload=formalize_payload,
        metadata={"problem_id": problem_id},
    )
    append_current_iteration_log(
        current_iteration_full_logs,
        stage="formalize",
        index=1,
        worker_meta=formalize_worker_meta,
    )
    return validate_formalizer_output(formalized, problem_id)


def request_prover_statement_formalization(
    *,
    worker_settings: Any,
    prover_statement_prompt: str,
    problem_id: str,
    stmt: str,
    open_rows: list[dict[str, Any]],
    theory_context: str,
    current_iteration_full_logs: list[dict[str, Any]],
) -> tuple[str, str, str, str, str, dict[str, Any]]:
    statement_payload: dict[str, Any] = {
        "problem_id": problem_id,
        "stmt": stmt,
        "theory_context": theory_context,
        "open_problems": open_rows,
    }
    formalized, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="prover_statement",
        system_prompt=prover_statement_prompt,
        payload=statement_payload,
        metadata={"problem_id": problem_id},
    )
    append_current_iteration_log(
        current_iteration_full_logs,
        stage="prover_statement",
        index=1,
        worker_meta=worker_meta,
    )
    result, lean_statement, theorem_name_stem, docstring_summary, notes = validate_prover_statement_output(formalized, problem_id)
    return result, lean_statement, theorem_name_stem, docstring_summary, notes, worker_meta


def resolve_solver_statement(
    *,
    prover_statement_worker_settings: Any,
    prover_statement_prompt_file: str,
    statement_verify_timeout_sec: int = 180,
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
) -> tuple[str, str, str, str, str, dict[str, Any]]:
    prover_statement_worker_meta: dict[str, Any] = {}
    if prover_statement_worker_settings is None:
        if original_stmt:
            return (
                original_stmt,
                "ok",
                "statement_target",
                "",
                "No prover_statement worker configured; using the existing statement directly.",
                prover_statement_worker_meta,
            )
        return "", "stuck", "", "", "Original statement is empty.", prover_statement_worker_meta

    emit_phase_log(
        phase_logs,
        "prover_statement",
        iteration=iteration,
        problem_id=problem_id,
        mode="worker",
    )
    prover_statement_prompt = load_prompt_text(prover_statement_prompt_file)
    stmt_started_monotonic = time.monotonic()
    stmt_started_at = iso_timestamp_now()
    try:
        result, formalized_stmt, theorem_name_stem, docstring_summary, notes, prover_statement_worker_meta = request_prover_statement_formalization(
            worker_settings=prover_statement_worker_settings,
            prover_statement_prompt=prover_statement_prompt,
            problem_id=problem_id,
            stmt=original_stmt,
            open_rows=open_rows,
            theory_context=theory_context,
            current_iteration_full_logs=current_iteration_full_logs,
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
        formalized_stmt = ""
        theorem_name_stem = ""
        docstring_summary = ""
        notes = f"prover_statement worker timeout: {exc}"
    else:
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
        )

    if result == "ok":
        theorem_name = build_theorem_name(problem_id, theorem_name_stem)
        verify_started_monotonic = time.monotonic()
        verify_started_at = iso_timestamp_now()
        verify_result = validate_solver_statement_with_lean(
            problem_id=problem_id,
            theorem_name=theorem_name,
            stmt=formalized_stmt,
            timeout_sec=statement_verify_timeout_sec,
        )
        update_compile_metrics(compile_metrics, verify_result)
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
            success=bool(verify_result.get("success", False)),
            result="verified" if bool(verify_result.get("success", False)) else "failed",
        )
        if not bool(verify_result.get("success", False)):
            lean_stderr = str(verify_result.get("stderr", "")).strip()
            lean_stdout = str(verify_result.get("stdout", "")).strip()
            lean_excerpt = (lean_stderr or lean_stdout).splitlines()[0] if (lean_stderr or lean_stdout) else "Lean statement validation failed"
            result = "stuck"
            formalized_stmt = ""
            theorem_name_stem = ""
            docstring_summary = ""
            notes = (
                f"{notes}\nLean statement validation failed before proof search: {lean_excerpt}"
                if notes
                else f"Lean statement validation failed before proof search: {lean_excerpt}"
            )

    solver_stmt = formalized_stmt if result == "ok" else ""
    emit_phase_log(
        phase_logs,
        "prover_statement_result",
        iteration=iteration,
        problem_id=problem_id,
        formalized=result == "ok",
        theorem_name_stem=theorem_name_stem,
        notes=notes,
    )
    return solver_stmt, result, theorem_name_stem, docstring_summary, notes, prover_statement_worker_meta


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
    max_candidates: int = 2,
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


def request_main_theorem_suggestion(
    *,
    worker_settings: Any,
    suggester_prompt: str,
    candidate_id: str,
    derived_entries: list[dict[str, str]],
    theory_context: str,
    open_rows: list[dict[str, Any]],
    current_iteration: int,
) -> tuple[tuple[str, str, str, str, str, list[str], list[str]], dict[str, Any]]:
    payload: dict[str, Any] = {
        "candidate_id": candidate_id,
        "current_iteration": current_iteration,
        "derived_theorems": [
            {
                "name": str(entry.get("name", "")),
                "statement": str(entry.get("statement", "")),
            }
            for entry in derived_entries
        ],
        "theory_context": theory_context,
        "open_problems": [
            {
                "problem_id": str(row.get("id", "")),
                "stmt": str(row.get("stmt", "")),
                "priority": open_problem_priority_label(row),
            }
            for row in open_rows[:20]
        ],
    }
    response, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="main_theorem_suggest",
        system_prompt=suggester_prompt,
        payload=payload,
        metadata={"candidate_id": candidate_id, "derived_theorem_count": len(derived_entries)},
    )
    return validate_main_theorem_suggestion_output(response, candidate_id), worker_meta


def request_main_theorem_plan(
    *,
    worker_settings: Any,
    planner_prompt: str,
    candidate_row: dict[str, Any],
    derived_entries: list[dict[str, str]],
    theory_context: str,
) -> tuple[tuple[str, str, str, list[str], list[str], str], dict[str, Any]]:
    payload: dict[str, Any] = {
        "candidate_id": str(candidate_row.get("candidate_id", "")),
        "statement": str(candidate_row.get("statement", "")),
        "theorem_name": str(candidate_row.get("theorem_name", "")),
        "docstring_summary": str(candidate_row.get("docstring_summary", "")),
        "rationale": str(candidate_row.get("rationale", "")),
        "supporting_theorems": list(candidate_row.get("supporting_theorems", [])),
        "missing_lemmas": list(candidate_row.get("missing_lemmas", [])),
        "derived_theorems": [
            {
                "name": str(entry.get("name", "")),
                "statement": str(entry.get("statement", "")),
            }
            for entry in shortlist_relevant_derived_entries(derived_entries, str(candidate_row.get("statement", "")), max_entries=8)
        ],
        "theory_context": theory_context,
    }
    response, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="main_theorem_plan",
        system_prompt=planner_prompt,
        payload=payload,
        metadata={"candidate_id": str(candidate_row.get("candidate_id", ""))},
    )
    return validate_main_theorem_plan_output(response, str(candidate_row.get("candidate_id", ""))), worker_meta


def request_open_problem_priorities(
    *,
    worker_settings: Any,
    prioritizer_prompt: str,
    tracked_rows: list[dict[str, Any]],
    derived_entries: list[dict[str, str]],
    current_iteration: int,
) -> tuple[list[dict[str, str]], dict[str, Any]]:
    expected_problem_ids = [str(row.get("id", "")) for row in tracked_rows]
    priority_payload: dict[str, Any] = {
        "current_iteration": current_iteration,
        "tracked_problems": [
            {
                "problem_id": str(row.get("id", "")),
                "stmt": str(row.get("stmt", "")),
                "src": str(row.get("src", "")),
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
    }
    prioritized, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="prioritize_open_problems",
        system_prompt=prioritizer_prompt,
        payload=priority_payload,
        metadata={"tracked_problem_count": len(tracked_rows), "derived_theorem_count": len(derived_entries)},
    )
    return validate_open_problem_priority_output(prioritized, expected_problem_ids), worker_meta


def force_refresh_open_problem_priorities(
    *,
    data_dir: Path,
    worker_settings: Any,
    prioritizer_prompt_file: str,
    derived_entries: list[dict[str, str]],
    current_iteration: int,
    failure_threshold: int,
) -> tuple[bool, str, dict[str, Any]]:
    if worker_settings is None:
        return False, "", {}

    open_path = data_dir / "open_problems.jsonl"
    archived_path = data_dir / ARCHIVED_PROBLEMS_FILENAME
    open_rows = [normalize_open_problem_row(row) for row in read_jsonl(open_path)]
    archived_rows = read_archived_problem_rows(data_dir)
    tracked_rows = open_rows + archived_rows
    if not tracked_rows:
        return False, "", {}

    prioritizer_prompt = load_prompt_text(prioritizer_prompt_file)
    try:
        priority_updates, worker_meta = request_open_problem_priorities(
            worker_settings=worker_settings,
            prioritizer_prompt=prioritizer_prompt,
            tracked_rows=tracked_rows,
            derived_entries=derived_entries,
            current_iteration=current_iteration,
        )
    except (RuntimeError, ValueError) as exc:
        return False, str(exc), {}

    tracked_rows = apply_open_problem_priorities(
        tracked_rows,
        priority_updates,
    )
    refreshed_open_rows, refreshed_archived_rows = split_active_and_archived_problem_queues(
        tracked_rows,
        failure_archive_threshold=failure_threshold,
    )
    write_jsonl_atomic(open_path, refreshed_open_rows)
    write_jsonl_atomic(archived_path, refreshed_archived_rows)
    return True, "", worker_meta


def attempt_formalization_until_timeout(
    *,
    problem_id: str,
    theorem_name: str,
    stmt: str,
    result: str,
    proof_sketch: str,
    counterexample_text: str,
    new_problems: list[str],
    scratch_file: Path,
    skip_verify: bool,
    formalize_worker_settings: Any,
    repair_worker_settings: Any,
    formalizer_prompt: str,
    repair_prompt: str,
    open_rows: list[dict[str, Any]],
    theory_context: str,
    verify_timeout_sec: int | None = 180,
    formalization_retry_budget_sec: int | None,
    memory_path: Path,
    current_iteration_full_logs: list[dict[str, Any]],
    initial_proof_text: str = "",
    phase_logger: Callable[..., None] | None = None,
    forbid_sorry: bool = False,
    max_repair_rounds: int | None = None,
    max_same_error_streak: int | None = None,
    run_id: str,
    session_type: str,
    iteration: int,
    phase_attempts_path: Path,
    compile_metrics: dict[str, Any],
) -> tuple[bool, str | None, str, str, str, list[str], str, str]:
    verify_success = False
    current_theorem_name = validate_theorem_name(theorem_name)
    current_stmt = stmt
    verify_error_excerpt = ""
    retained_new_problems = list(new_problems)
    proof_text = initial_proof_text
    attempted_strengthened_statements = {normalize_stmt_text(current_stmt)}
    best_verified_candidate: dict[str, Any] | None = None

    if result not in {"proof", "counterexample"}:
        # Preserve stuck/counterexample exploration history so future timeout handling
        # can mine subgoal candidates from prior reasoning.
        persisted_history = load_formalization_memory(memory_path, problem_id)
        persisted_history.append(
            {
                "result": result,
                "verify_success": verify_success,
                "proof_sketch": proof_sketch,
                "proof_text": proof_text,
                "counterexample_text": counterexample_text,
                "lean_error_excerpt": verify_error_excerpt,
                "lean_error_fingerprint": "non_formalized_result",
                "new_problems": list(new_problems)[:2],
            }
        )
        save_formalization_memory(memory_path, problem_id, persisted_history)
        return verify_success, current_theorem_name, result, proof_text, counterexample_text, new_problems, verify_error_excerpt, current_stmt

    if not proof_text.strip():
        if formalize_worker_settings is None:
            persisted_history = load_formalization_memory(memory_path, problem_id)
            persisted_history.append(
                {
                    "result": result,
                    "verify_success": verify_success,
                    "proof_sketch": proof_sketch,
                    "proof_text": proof_text,
                    "counterexample_text": counterexample_text,
                    "lean_error_excerpt": verify_error_excerpt,
                    "lean_error_fingerprint": "formalizer_unavailable",
                    "new_problems": list(new_problems)[:2],
                }
            )
            save_formalization_memory(memory_path, problem_id, persisted_history)
            return verify_success, current_theorem_name, "stuck", proof_text, counterexample_text, new_problems, verify_error_excerpt, current_stmt

        try:
            same_problem_history_tail = load_formalization_memory(memory_path, problem_id)[-8:]
            proof_lean_started_monotonic = time.monotonic()
            proof_lean_started_at = iso_timestamp_now()
            result, proof_sketch, proof_text, counterexample_text = request_initial_formalization(
                formalize_worker_settings=formalize_worker_settings,
                formalizer_prompt=formalizer_prompt,
                problem_id=problem_id,
                stmt=current_stmt,
                result=result,
                proof_sketch=proof_sketch,
                counterexample_text=counterexample_text,
                open_rows=open_rows,
                theory_context=theory_context,
                current_iteration_full_logs=current_iteration_full_logs,
                same_problem_history_tail=same_problem_history_tail,
            )
        except RuntimeError as exc:
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type=session_type,
                iteration=iteration,
                entity_id=problem_id,
                phase="proof_lean",
                worker_task="formalize",
                started_at=proof_lean_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(proof_lean_started_monotonic),
                success=False,
                result="timeout" if is_worker_timeout_error(exc) else "error",
                timeout=is_worker_timeout_error(exc),
                error=str(exc),
            )
            if is_worker_timeout_error(exc):
                persisted_history = load_formalization_memory(memory_path, problem_id)
                verify_error_excerpt = f"formalize worker timeout: {exc}"
                persisted_history.append(
                    {
                        "result": "stuck",
                        "verify_success": verify_success,
                        "proof_sketch": proof_sketch,
                        "proof_text": proof_text,
                        "counterexample_text": counterexample_text,
                        "lean_error_excerpt": verify_error_excerpt,
                        "lean_error_fingerprint": "formalizer_timeout",
                        "new_problems": list(new_problems)[:2],
                    }
                )
                save_formalization_memory(memory_path, problem_id, persisted_history)
                return verify_success, current_theorem_name, "stuck", proof_text, counterexample_text, new_problems, verify_error_excerpt, current_stmt
            raise
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type=session_type,
            iteration=iteration,
            entity_id=problem_id,
            phase="proof_lean",
            worker_task="formalize",
            started_at=proof_lean_started_at,
            finished_at=iso_timestamp_now(),
            duration_ms=monotonic_duration_ms(proof_lean_started_monotonic),
            success=result in {"proof", "counterexample"},
            result=result,
        )
        if result not in {"proof", "counterexample"}:
            persisted_history = load_formalization_memory(memory_path, problem_id)
            persisted_history.append(
                {
                    "result": result,
                    "verify_success": verify_success,
                    "proof_sketch": proof_sketch,
                    "proof_text": proof_text,
                    "counterexample_text": counterexample_text,
                    "lean_error_excerpt": verify_error_excerpt,
                    "lean_error_fingerprint": "formalizer_returned_stuck",
                    "new_problems": list(new_problems)[:2],
                }
            )
            save_formalization_memory(memory_path, problem_id, persisted_history)
            return verify_success, current_theorem_name, result, proof_text, counterexample_text, new_problems, verify_error_excerpt, current_stmt

    deadline = (
        None
        if formalization_retry_budget_sec is None
        else time.monotonic() + max(1, formalization_retry_budget_sec)
    )
    persisted_history = load_formalization_memory(memory_path, problem_id)
    repair_round = 0
    repair_history: list[dict[str, Any]] = list(persisted_history)
    last_error_fingerprint = ""
    same_error_streak = 0

    while True:
        if phase_logger is not None:
            phase_logger(
                phase="formalize_and_verify",
                status="begin",
                problem_id=problem_id,
                result=result,
                repair_round=repair_round,
            )
        theorem_name, scratch_code = formalize_to_scratch(
            theorem_name=current_theorem_name,
            stmt=current_stmt,
            mode=result,
            proof_text=proof_text,
            counterexample_text=counterexample_text,
        )

        lean_diagnostics = ""
        verify_stderr_text = ""
        verify_stdout_text = ""
        scratch_file.write_text(scratch_code, encoding="utf-8")
        if skip_verify:
            verify_success = True
            verify_error_excerpt = ""
            verify_error_analysis = {
                "fingerprint": "verify_skipped",
                "categories": ["verify_skipped"],
                "top_lines": [],
            }
        else:
            verify_started_at = iso_timestamp_now()
            verify_started_monotonic = time.monotonic()
            verify_result = verify_scratch(problem_id, result, scratch_file, timeout_sec=verify_timeout_sec)
            update_compile_metrics(compile_metrics, verify_result)
            verify_success = bool(verify_result.get("success", False))
            verify_stderr_text = str(verify_result.get("stderr", ""))
            verify_stdout_text = str(verify_result.get("stdout", ""))
            lean_diagnostics = (verify_stderr_text + "\n" + verify_stdout_text).strip()
            if not verify_success:
                verify_stderr = verify_stderr_text.strip()
                verify_stdout = verify_stdout_text.strip()
                verify_error_excerpt = (verify_stderr or verify_stdout).splitlines()[0] if (verify_stderr or verify_stdout) else "Lean verification failed"
            else:
                verify_error_excerpt = ""
            verify_error_analysis = analyze_lean_failure(
                verify_stderr_text,
                verify_stdout_text,
            )
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type=session_type,
                iteration=iteration,
                entity_id=problem_id,
                phase="verify",
                worker_task="scratch_verify",
                started_at=verify_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=int(verify_result.get("duration_ms", monotonic_duration_ms(verify_started_monotonic)) or 0),
                success=verify_success,
                result="verified" if verify_success else "failed",
            )

        if phase_logger is not None:
            phase_logger(
                phase="formalize_and_verify_result",
                problem_id=problem_id,
                result=result,
                repair_round=repair_round,
                verify_success=verify_success,
                error_fingerprint=str(verify_error_analysis.get("fingerprint", "")),
            )

        if verify_success:
            if forbid_sorry and file_contains_sorry(scratch_file):
                verify_success = False
                verify_error_excerpt = "Lean verification succeeded but proof still contains sorry"
                verify_error_analysis = {
                    "fingerprint": "main_theorem_contains_sorry",
                    "categories": ["contains_sorry"],
                    "top_lines": [verify_error_excerpt],
                }
            else:
                last_error_fingerprint = ""
                same_error_streak = 0
        if verify_success:
            best_verified_candidate = {
                "stmt": current_stmt,
                "result": result,
                "proof_text": proof_text,
                "counterexample_text": counterexample_text,
                "new_problems": list(retained_new_problems),
                "verify_error_excerpt": verify_error_excerpt,
            }
            unused_names = extract_unused_variable_names(verify_stderr_text, verify_stdout_text)
            strengthened_stmt = (
                prune_unused_binders_from_statement(current_stmt, unused_names)
                if result == "proof" and not skip_verify
                else current_stmt
            )
            strengthened_norm = normalize_stmt_text(strengthened_stmt)
            if (
                result == "proof"
                and strengthened_stmt != current_stmt
                and strengthened_norm not in attempted_strengthened_statements
            ):
                attempted_strengthened_statements.add(strengthened_norm)
                current_stmt = strengthened_stmt
                continue
            success_fingerprint = str(verify_error_analysis.get("fingerprint", "verified"))
            repair_history.append(
                {
                    "result": result,
                    "verify_success": True,
                    "proof_sketch": proof_sketch,
                    "proof_text": proof_text,
                    "counterexample_text": counterexample_text,
                    "lean_error_excerpt": verify_error_excerpt,
                    "lean_error_fingerprint": success_fingerprint,
                    "new_problems": list(retained_new_problems)[:2],
                }
            )
            if len(repair_history) > 20:
                repair_history = repair_history[-20:]
            save_formalization_memory(memory_path, problem_id, repair_history)
            return (
                verify_success,
                current_theorem_name,
                result,
                proof_text,
                counterexample_text,
                retained_new_problems,
                verify_error_excerpt,
                current_stmt,
            )

        if repair_worker_settings is None or (deadline is not None and time.monotonic() >= deadline):
            save_formalization_memory(memory_path, problem_id, repair_history)
            if best_verified_candidate is not None:
                return (
                    True,
                    current_theorem_name,
                    str(best_verified_candidate["result"]),
                    str(best_verified_candidate["proof_text"]),
                    str(best_verified_candidate["counterexample_text"]),
                    list(best_verified_candidate["new_problems"]),
                    str(best_verified_candidate["verify_error_excerpt"]),
                    str(best_verified_candidate["stmt"]),
                )
            return (
                verify_success,
                current_theorem_name,
                result,
                proof_text,
                counterexample_text,
                retained_new_problems,
                verify_error_excerpt,
                current_stmt,
            )

        error_fingerprint = str(verify_error_analysis.get("fingerprint", "no_diagnostics"))
        error_categories = verify_error_analysis.get("categories", [])
        lean_error_top_lines = verify_error_analysis.get("top_lines", [])
        if error_fingerprint == last_error_fingerprint:
            same_error_streak += 1
        else:
            last_error_fingerprint = error_fingerprint
            same_error_streak = 1
        if best_verified_candidate is not None and normalize_stmt_text(current_stmt) != normalize_stmt_text(str(best_verified_candidate["stmt"])):
            retry_instruction = (
                "The previous theorem already verified. A stronger candidate statement was formed by removing unused binders "
                "from `stmt`. Try to prove this stronger `stmt`; if the old proof no longer fits, revise `proof_text` minimally "
                "so it proves the new statement. proof_text must be Lean tactic code only."
            )
        else:
            retry_instruction = (
                "Previous proof/counterexample failed Lean formalization or verification. "
                "Read the Lean diagnostics carefully. Revise proof_sketch if the strategy was wrong, "
                "then fix proof_text to match. proof_text must be Lean tactic code only."
            )

        repair_history.append(
            {
                "result": result,
                "verify_success": verify_success,
                "proof_sketch": proof_sketch,
                "proof_text": proof_text,
                "counterexample_text": counterexample_text,
                "lean_error_excerpt": verify_error_excerpt,
                "lean_error_fingerprint": error_fingerprint,
                "new_problems": list(new_problems)[:2],
            }
        )
        if len(repair_history) > 4:
            repair_history = repair_history[-20:]
        save_formalization_memory(memory_path, problem_id, repair_history)

        repair_round += 1
        if max_repair_rounds is not None and repair_round > max_repair_rounds:
            save_formalization_memory(memory_path, problem_id, repair_history)
            if best_verified_candidate is not None:
                return (
                    True,
                    current_theorem_name,
                    str(best_verified_candidate["result"]),
                    str(best_verified_candidate["proof_text"]),
                    str(best_verified_candidate["counterexample_text"]),
                    list(best_verified_candidate["new_problems"]),
                    str(best_verified_candidate["verify_error_excerpt"]),
                    str(best_verified_candidate["stmt"]),
                )
            return (
                False,
                current_theorem_name,
                result,
                proof_text,
                counterexample_text,
                retained_new_problems,
                verify_error_excerpt,
                current_stmt,
            )
        if max_same_error_streak is not None and same_error_streak > max_same_error_streak:
            save_formalization_memory(memory_path, problem_id, repair_history)
            if best_verified_candidate is not None:
                return (
                    True,
                    current_theorem_name,
                    str(best_verified_candidate["result"]),
                    str(best_verified_candidate["proof_text"]),
                    str(best_verified_candidate["counterexample_text"]),
                    list(best_verified_candidate["new_problems"]),
                    str(best_verified_candidate["verify_error_excerpt"]),
                    str(best_verified_candidate["stmt"]),
                )
            return (
                False,
                current_theorem_name,
                result,
                proof_text,
                counterexample_text,
                retained_new_problems,
                verify_error_excerpt,
                current_stmt,
            )
        if phase_logger is not None:
            phase_logger(
                phase="repair",
                problem_id=problem_id,
                repair_round=repair_round,
                error_fingerprint=error_fingerprint,
            )
        repair_payload: dict[str, Any] = {
            "problem_id": problem_id,
            "stmt": current_stmt,
            "theory_context": theory_context,
            "new_problem_generation_policy": {
                "prefer_subgoals_when_stuck": True,
                "avoid_generalization_when_stuck": True,
                "prefer_intermediate_lemmas": True,
                "avoid_direct_axiom_instantiation": True,
                "avoid_variable_renaming_only": True,
                "target_novelty": "medium_or_high",
            },
            "retry_instruction": retry_instruction,
            "error_fingerprint": error_fingerprint,
            "error_categories": error_categories,
            "previous_result": result,
            "previous_proof_sketch": proof_sketch,
            "previous_proof_text": proof_text,
            "previous_counterexample_text": counterexample_text,
            "previous_new_problems": new_problems,
            "repair_history_tail": repair_history[-8:],
            "lean_error_excerpt": verify_error_excerpt,
            "lean_error_top_lines": lean_error_top_lines,
            "lean_diagnostics": "\n".join(lean_diagnostics.splitlines()[:60]),
            "current_scratch_code": scratch_code or "",
            "mathlib_import_in_scratch": True,
        }

        try:
            repair_started_monotonic = time.monotonic()
            repair_started_at = iso_timestamp_now()
            repaired, repair_worker_meta = invoke_worker_json(
                settings=repair_worker_settings,
                task_type="repair",
                system_prompt=repair_prompt,
                payload=repair_payload,
                metadata={"problem_id": problem_id, "repair_round": repair_round},
            )
            append_current_iteration_log(
                current_iteration_full_logs,
                stage="repair",
                index=repair_round,
                worker_meta=repair_worker_meta,
            )
        except RuntimeError as exc:
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type=session_type,
                iteration=iteration,
                entity_id=problem_id,
                phase="repair_lean",
                worker_task="repair",
                started_at=repair_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(repair_started_monotonic),
                success=False,
                result="timeout" if is_worker_timeout_error(exc) else "error",
                timeout=is_worker_timeout_error(exc),
                error=str(exc),
            )
            if is_worker_timeout_error(exc):
                verify_error_excerpt = f"repair worker timeout: {exc}"
                save_formalization_memory(memory_path, problem_id, repair_history)
                if best_verified_candidate is not None:
                    return (
                        True,
                        current_theorem_name,
                        str(best_verified_candidate["result"]),
                        str(best_verified_candidate["proof_text"]),
                        str(best_verified_candidate["counterexample_text"]),
                        list(best_verified_candidate["new_problems"]),
                        str(best_verified_candidate["verify_error_excerpt"]),
                        str(best_verified_candidate["stmt"]),
                    )
                return (
                    verify_success,
                    theorem_name,
                    result,
                    proof_text,
                    counterexample_text,
                    retained_new_problems,
                    verify_error_excerpt,
                    current_stmt,
                )
            raise
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type=session_type,
            iteration=iteration,
            entity_id=problem_id,
            phase="repair_lean",
            worker_task="repair",
            started_at=repair_started_at,
            finished_at=iso_timestamp_now(),
            duration_ms=monotonic_duration_ms(repair_started_monotonic),
            success=True,
            result="ok",
        )
        try:
            result, proof_sketch, proof_text, counterexample_text = validate_formalizer_output(repaired, problem_id)
        except ValueError as exc:
            verify_error_excerpt = f"repair output invalid: {exc}"
            continue
        if result not in {"proof", "counterexample"}:
            save_formalization_memory(memory_path, problem_id, repair_history)
            if best_verified_candidate is not None:
                return (
                    True,
                    current_theorem_name,
                    str(best_verified_candidate["result"]),
                    str(best_verified_candidate["proof_text"]),
                    str(best_verified_candidate["counterexample_text"]),
                    list(best_verified_candidate["new_problems"]),
                    str(best_verified_candidate["verify_error_excerpt"]),
                    str(best_verified_candidate["stmt"]),
                )
            return (
                False,
                current_theorem_name,
                result,
                proof_text,
                counterexample_text,
                retained_new_problems,
                verify_error_excerpt,
                current_stmt,
            )

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
    seed_rows = [normalize_open_problem_row(row) for row in read_jsonl(seeds_file)]
    if not seed_rows:
        raise ValueError(f"Seeds file is empty: {seeds_file}")

    data_dir.mkdir(parents=True, exist_ok=True)
    write_jsonl_atomic(data_dir / "open_problems.jsonl", seed_rows)
    write_jsonl_atomic(archived_problems_file, [])
    write_jsonl_atomic(data_dir / "solved_problems.jsonl", [])
    write_jsonl_atomic(data_dir / "counterexamples.jsonl", [])
    (data_dir / LEGACY_DEFERRED_PROBLEMS_FILENAME).unlink(missing_ok=True)
    (data_dir / LEGACY_PRUNED_OPEN_PROBLEMS_FILENAME).unlink(missing_ok=True)

    if reset_scratch:
        scratch_file.parent.mkdir(parents=True, exist_ok=True)
        scratch_file.write_text(SCRATCH_TEMPLATE, encoding="utf-8")

    if reset_derived:
        derived_file.parent.mkdir(parents=True, exist_ok=True)
        derived_file.write_text(DERIVED_TEMPLATE, encoding="utf-8")
        for cleanup_file in derived_cleanup_files:
            cleanup_file.unlink(missing_ok=True)

    if reset_formalization_memory:
        formalization_memory_file.parent.mkdir(parents=True, exist_ok=True)
        formalization_memory_file.write_text("{}\n", encoding="utf-8")


def run_manual_main_theorem_check(
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
    suggest_prompt_file: str,
    plan_prompt_file: str,
    post_expand_prompt_file: str,
    prioritize_open_problems_worker_settings: Any,
    prioritize_open_problems_prompt_file: str,
    current_iteration: int,
    skip_verify: bool,
    verify_timeout_sec: int | None,
    formalization_retry_budget_sec: int | None,
    max_repair_rounds: int,
    max_same_error_streak: int,
    post_expand_count: int,
    failure_threshold: int,
    phase_logs: bool,
    run_id: str,
    phase_attempts_path: Path,
    compile_metrics: dict[str, Any],
) -> dict[str, Any]:
    if worker_settings is None:
        emit_phase_log(
            phase_logs,
            "main_theorem_check",
            iteration=current_iteration,
            status="worker_unavailable",
        )
        return {
            "status": "main_theorem_worker_unavailable",
            "processed": False,
            "verify_success": False,
        }

    suggest_prompt = load_prompt_text(suggest_prompt_file)
    open_rows = [normalize_open_problem_row(row) for row in read_jsonl(data_dir / "open_problems.jsonl")]
    candidate_id = "mt_manual"
    emit_phase_log(
        phase_logs,
        "main_theorem_suggest",
        iteration=current_iteration,
        candidate_id=candidate_id,
        derived_theorem_count=len(derived_entries),
        open_problem_count=len(open_rows),
    )
    suggest_started_monotonic = time.monotonic()
    suggest_started_at = iso_timestamp_now()
    try:
        (
            result,
            statement,
            theorem_name_stem,
            docstring_summary,
            rationale,
            supporting_theorems,
            missing_lemmas,
        ), suggest_worker_meta = request_main_theorem_suggestion(
            worker_settings=worker_settings,
            suggester_prompt=suggest_prompt,
            candidate_id=candidate_id,
            derived_entries=derived_entries,
            theory_context=base_theory_context,
            open_rows=open_rows,
            current_iteration=current_iteration,
        )
    except (RuntimeError, ValueError) as exc:
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
            error=str(exc),
        )
        emit_phase_log(
            phase_logs,
            "main_theorem_suggest_result",
            iteration=current_iteration,
            candidate_id=candidate_id,
            status="error",
            error=str(exc),
        )
        return {
            "status": "main_theorem_suggest_error",
            "processed": False,
            "verify_success": False,
            "error": str(exc),
        }
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
        success=result == "ok",
        result=result,
    )

    emit_phase_log(
        phase_logs,
        "main_theorem_suggest_result",
        iteration=current_iteration,
        candidate_id=candidate_id,
        status=result,
    )
    if result != "ok":
        return {
            "status": "main_theorem_suggest_stuck",
            "processed": False,
            "verify_success": False,
        }

    report = process_manual_main_theorem(
        candidate_id=candidate_id,
        statement=statement,
        theorem_name=f"main_thm_{theorem_name_stem}",
        docstring_summary=docstring_summary,
        rationale=rationale,
        supporting_theorems=supporting_theorems,
        missing_lemmas=missing_lemmas,
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
        plan_prompt_file=plan_prompt_file,
        post_expand_prompt_file=post_expand_prompt_file,
        prioritize_open_problems_worker_settings=prioritize_open_problems_worker_settings,
        prioritize_open_problems_prompt_file=prioritize_open_problems_prompt_file,
        current_iteration=current_iteration,
        skip_verify=skip_verify,
        verify_timeout_sec=verify_timeout_sec,
        formalization_retry_budget_sec=formalization_retry_budget_sec,
        max_repair_rounds=max_repair_rounds,
        max_same_error_streak=max_same_error_streak,
        post_expand_count=post_expand_count,
        failure_threshold=failure_threshold,
        phase_logs=phase_logs,
        run_id=run_id,
        phase_attempts_path=phase_attempts_path,
        compile_metrics=compile_metrics,
    )
    report["suggested_statement"] = statement
    report["suggested_rationale"] = rationale
    return report


def process_manual_main_theorem(
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
    plan_prompt_file: str,
    post_expand_prompt_file: str,
    prioritize_open_problems_worker_settings: Any,
    prioritize_open_problems_prompt_file: str,
    current_iteration: int,
    skip_verify: bool,
    verify_timeout_sec: int | None,
    formalization_retry_budget_sec: int | None,
    max_repair_rounds: int,
    max_same_error_streak: int,
    post_expand_count: int,
    failure_threshold: int,
    phase_logs: bool,
    run_id: str,
    phase_attempts_path: Path,
    compile_metrics: dict[str, Any],
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
    plan_summary = ""
    proof_sketch = ""
    plan_notes = ""
    intermediate_lemmas: list[str] = []
    plan_worker_meta: dict[str, Any] = {}

    if worker_settings is not None:
        emit_phase_log(
            phase_logs,
            "main_theorem_plan",
            iteration=current_iteration,
            candidate_id=candidate_id,
            theorem_name=theorem_name,
        )
        planner_prompt = load_prompt_text(plan_prompt_file)
        plan_started_monotonic = time.monotonic()
        plan_started_at = iso_timestamp_now()
        try:
            (
                plan_result,
                generated_plan_summary,
                generated_proof_sketch,
                plan_supporting_theorems,
                intermediate_lemmas,
                plan_notes,
            ), plan_worker_meta = request_main_theorem_plan(
                worker_settings=worker_settings,
                planner_prompt=planner_prompt,
                candidate_row={
                    "candidate_id": candidate_id,
                    "statement": statement,
                    "theorem_name": theorem_name,
                    "docstring_summary": docstring_summary,
                    "rationale": rationale,
                    "supporting_theorems": supporting_theorems,
                    "missing_lemmas": missing_lemmas,
                },
                derived_entries=derived_entries,
                theory_context=theorem_context,
            )
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type="main_theorem_session",
                iteration=current_iteration,
                entity_id=candidate_id,
                phase="main_theorem_plan",
                worker_task="main_theorem_plan",
                started_at=plan_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(plan_started_monotonic),
                success=plan_result == "ok",
                result=plan_result,
            )
            if plan_result == "ok":
                plan_summary = generated_plan_summary
                proof_sketch = generated_proof_sketch
                supporting_theorems = plan_supporting_theorems or list(supporting_theorems)
            emit_phase_log(
                phase_logs,
                "main_theorem_plan_result",
                iteration=current_iteration,
                candidate_id=candidate_id,
                status=plan_result,
            )
        except (RuntimeError, ValueError) as exc:
            plan_notes = f"main theorem plan failed: {exc}"
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type="main_theorem_session",
                iteration=current_iteration,
                entity_id=candidate_id,
                phase="main_theorem_plan",
                worker_task="main_theorem_plan",
                started_at=plan_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(plan_started_monotonic),
                success=False,
                result="error",
                error=str(exc),
            )
            emit_phase_log(
                phase_logs,
                "main_theorem_plan_result",
                iteration=current_iteration,
                candidate_id=candidate_id,
                status="error",
                error=str(exc),
            )

    if not proof_sketch:
        proof_sketch = rationale.strip() or f"Prove {theorem_name} from the current Derived.lean cluster."
    if plan_summary:
        theorem_context += f"\n\n-- Main theorem proof plan:\n-- {plan_summary}"
    if intermediate_lemmas:
        theorem_context += "\n-- Intermediate lemmas:\n"
        theorem_context += "\n".join(f"-- {item}" for item in intermediate_lemmas)
    if plan_notes:
        theorem_context += f"\n-- Planner notes: {plan_notes}"

    formalizer_prompt = load_prompt_text(formalizer_prompt_file) if formalize_worker_settings is not None else ""
    repair_prompt = load_prompt_text(repair_prompt_file) if repair_worker_settings is not None else ""
    verify_success, _, result, proof_text, counterexample_text, _, verify_error_excerpt, final_stmt = attempt_formalization_until_timeout(
        problem_id=candidate_id,
        theorem_name=theorem_name,
        stmt=statement,
        result="proof",
        proof_sketch=proof_sketch,
        counterexample_text="",
        new_problems=[],
        scratch_file=scratch_file,
        skip_verify=skip_verify,
        formalize_worker_settings=formalize_worker_settings,
        repair_worker_settings=repair_worker_settings,
        formalizer_prompt=formalizer_prompt,
        repair_prompt=repair_prompt,
        open_rows=[normalize_open_problem_row(row) for row in read_jsonl(data_dir / "open_problems.jsonl")],
        theory_context=theorem_context,
        verify_timeout_sec=verify_timeout_sec,
        formalization_retry_budget_sec=formalization_retry_budget_sec,
        memory_path=formalization_memory_path,
        current_iteration_full_logs=current_iteration_full_logs,
        initial_proof_text="",
        phase_logger=(lambda **fields: emit_phase_log(phase_logs, iteration=current_iteration, **fields)),
        forbid_sorry=True,
        max_repair_rounds=max_repair_rounds,
        max_same_error_streak=max_same_error_streak,
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

    if not verify_success or result != "proof":
        return {
            "processed": True,
            "candidate_id": candidate_id,
            "status": "blocked",
            "verify_success": False,
            "verify_error_excerpt": verify_error_excerpt,
            "plan_summary": plan_summary,
        }

    theorem_code = append_verified_theorem_from_scratch(
        scratch_path=scratch_file,
        derived_file=derived_file,
        derived_entries=derived_entries,
        docstring=docstring_summary,
    )
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
        for entry in derived_entries
        if str(entry.get("name", "")).strip()
    }
    append_theorem_reuse_memory_entry(
        data_dir / "theorem_reuse_memory.json",
        {
            "candidate_id": candidate_id,
            "theorem_name": theorem_name,
            "statement": final_stmt.strip() or statement,
            "docstring_summary": docstring_summary,
            "rationale": rationale,
            "plan_summary": plan_summary,
            "supporting_theorems": [
                theorem for theorem in supporting_theorems
                if theorem in known_theorem_names
            ],
            "intermediate_lemmas": intermediate_lemmas,
            "iteration": current_iteration,
            "appended_to_derived": bool(theorem_code),
        },
    )

    post_new_problems: list[str] = []
    post_expand_error = ""
    post_expand_worker_meta: dict[str, Any] = {}
    theorem_context = build_problem_theory_context(base_theory_context, derived_entries, final_stmt)
    if worker_settings is not None and theorem_code:
        emit_phase_log(
            phase_logs,
            "post_theorem_expand",
            iteration=current_iteration,
            candidate_id=candidate_id,
            theorem_name=theorem_name,
        )
        post_expand_prompt = load_prompt_text(post_expand_prompt_file)
        post_expand_started_monotonic = time.monotonic()
        post_expand_started_at = iso_timestamp_now()
        try:
            post_candidates, post_expand_worker_meta = request_expand_candidates(
                worker_settings=worker_settings,
                expand_prompt=post_expand_prompt,
                task_type="post_theorem_expand",
                problem_id=candidate_id,
                stmt=final_stmt,
                original_stmt=statement,
                result="proof",
                verify_success=True,
                theory_context=theorem_context,
                open_rows=[normalize_open_problem_row(row) for row in read_jsonl(data_dir / "open_problems.jsonl")],
                existing_new_problems=[],
                verify_error_excerpt="",
                current_iteration_full_logs=current_iteration_full_logs,
                same_problem_history_tail=load_formalization_memory(formalization_memory_path, candidate_id)[-8:],
                max_candidates=post_expand_count,
            )
            post_new_problems = [item["statement"] for item in post_candidates]
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
                generated_problem_count=len(post_new_problems),
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

    enqueue_report = enqueue_new_problems(
        data_dir,
        post_new_problems,
        source="post_theorem_expand",
        source_details={
            "parent_entity_id": theorem_name,
            "parent_entity_type": "theorem",
            "generated_by_phase": "post_theorem_expand",
            "created_at_run_id": run_id,
            "created_at_iteration": current_iteration,
            "created_in_session_type": "main_theorem_session",
        },
        failure_threshold=failure_threshold,
    )
    priority_refresh_ran, priority_refresh_error, priority_refresh_worker_meta = force_refresh_open_problem_priorities(
        data_dir=data_dir,
        worker_settings=prioritize_open_problems_worker_settings,
        prioritizer_prompt_file=prioritize_open_problems_prompt_file,
        derived_entries=derived_entries,
        current_iteration=current_iteration,
        failure_threshold=failure_threshold,
    )
    return {
        "processed": True,
        "candidate_id": candidate_id,
        "status": "proved",
        "verify_success": True,
        "theorem_name": theorem_name,
        "statement": final_stmt.strip() or statement,
        "supporting_theorems": list(supporting_theorems),
        "post_theorem_new_problems": post_new_problems,
        "post_theorem_expand_error": post_expand_error,
        "priority_refresh_ran": priority_refresh_ran,
        "priority_refresh_error": priority_refresh_error,
        "enqueue_added_problem_ids": list(enqueue_report.get("added_problem_ids", [])),
        "enqueue_added_problem_rows": list(enqueue_report.get("added_problem_rows", [])),
    }


def prebuild_lean_project() -> list[dict[str, Any]]:
    """Build Lean artifacts once during initialization.

    Build only the stable library modules here.
    Scratch.lean is a transient verification target and should remain outside
    initialization builds so a broken scratch proof does not block the loop.
    """
    results: list[dict[str, Any]] = []
    for target in ("AutomatedTheoryConstruction.Theory", "AutomatedTheoryConstruction.Derived"):
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


def next_main_theorem_trigger_count(current_count: int, interval: int) -> int | None:
    if interval <= 0:
        return None
    return ((current_count // interval) + 1) * interval


def main() -> None:
    parser = argparse.ArgumentParser(description="Run the minimal prototype loop.")
    parser.add_argument("--initialize-on-start", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--phase-logs", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--max-iterations", type=int)
    parser.add_argument("--enable-worker", action="store_true")
    parser.add_argument("--worker-command")
    parser.add_argument("--worker-timeout", type=int)
    parser.add_argument("--skip-verify", action="store_true")
    parser.add_argument("--open-problem-failure-threshold", type=int, default=2)
    parser.add_argument("--main-theorem-interval", type=int, default=0)
    parser.add_argument("--main-theorem-formalize-worker-timeout", type=int)
    parser.add_argument("--main-theorem-repair-worker-timeout", type=int)
    parser.add_argument("--main-theorem-verify-timeout", type=int, default=600)
    parser.add_argument("--main-theorem-formalization-retry-budget-sec", type=int, default=3600)
    parser.add_argument("--priority-refresh-theorem-interval", type=int, default=5)
    args = parser.parse_args()
    if args.max_iterations is not None and args.max_iterations < 0:
        raise ValueError("--max-iterations must be >= 0")
    if args.open_problem_failure_threshold < 0:
        raise ValueError("--open-problem-failure-threshold must be >= 0")
    if args.main_theorem_interval < 0:
        raise ValueError("--main-theorem-interval must be >= 0")
    if args.main_theorem_formalize_worker_timeout is not None and args.main_theorem_formalize_worker_timeout < 0:
        raise ValueError("--main-theorem-formalize-worker-timeout must be >= 0")
    if args.main_theorem_repair_worker_timeout is not None and args.main_theorem_repair_worker_timeout < 0:
        raise ValueError("--main-theorem-repair-worker-timeout must be >= 0")
    if args.main_theorem_verify_timeout < 0:
        raise ValueError("--main-theorem-verify-timeout must be >= 0")
    if args.main_theorem_formalization_retry_budget_sec < 0:
        raise ValueError("--main-theorem-formalization-retry-budget-sec must be >= 0")
    if args.priority_refresh_theorem_interval < 0:
        raise ValueError("--priority-refresh-theorem-interval must be >= 0")

    # Fixed runtime paths and hidden compatibility defaults.
    args.data_dir = "data"
    args.seeds_file = "AutomatedTheoryConstruction/seeds.jsonl"
    args.scratch_file = "AutomatedTheoryConstruction/Scratch.lean"
    args.derived_file = "AutomatedTheoryConstruction/Derived.lean"
    args.reset_scratch_on_start = True
    args.reset_derived_on_start = True
    args.theory_file = "AutomatedTheoryConstruction/Theory.lean"
    args.prover_statement_prompt_file = "prompts/prover_statement_formalizer.md"
    args.formalizer_prompt_file = "prompts/formalizer_simple.md"
    args.repair_prompt_file = None
    args.prioritize_open_problems_prompt_file = "prompts/open_problem_prioritizer.md"
    args.main_theorem_suggest_prompt_file = "prompts/main_theorem_suggester.md"
    args.main_theorem_plan_prompt_file = "prompts/main_theorem_planner.md"
    args.main_theorem_post_expand_prompt_file = "prompts/post_theorem_expander.md"
    # Problem selection is deterministic local logic; the worker handles priority refresh and prover/formalize stages.
    args.prover_prompt_file = "prompts/prover_simple.md"
    args.expander_prompt_file = "prompts/new_problem_expander.md"
    args.prover_retries = 2
    args.formalization_retry_budget_sec = 300
    args.formalization_memory_file = "data/formalization_memory.json"
    args.archived_problems_file = f"data/{ARCHIVED_PROBLEMS_FILENAME}"
    args.reset_formalization_memory_on_start = True
    data_dir = Path(args.data_dir)
    scratch_file = Path(args.scratch_file)
    memory_path = Path(args.formalization_memory_file)
    archived_problems_path = Path(args.archived_problems_file)
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
    run_status = "started"
    recorded_problem_ids: set[str] = set()
    recorded_theorem_names: set[str] = set()

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
            seeds_file=Path(args.seeds_file),
            scratch_file=scratch_file,
            reset_scratch=args.reset_scratch_on_start,
            derived_file=Path(args.derived_file),
            derived_cleanup_files=(
                Path("AutomatedTheoryConstruction/Derived.refactored.preview.lean"),
                Path("AutomatedTheoryConstruction/Derived.refactored.reviewed.lean"),
            ),
            reset_derived=args.reset_derived_on_start,
            formalization_memory_file=memory_path,
            reset_formalization_memory=args.reset_formalization_memory_on_start,
            archived_problems_file=archived_problems_path,
        )
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

    _, base_theory_context = load_theory_context(Path(args.theory_file))
    derived_path = Path(args.derived_file)
    derived_entries = extract_derived_theorem_entries(derived_path)
    open_path = data_dir / "open_problems.jsonl"
    initial_problem_rows = [normalize_open_problem_row(row) for row in read_jsonl(open_path)]
    initial_problem_rows.extend(read_archived_problem_rows(data_dir))
    record_problem_rows(
        initial_problem_rows,
        iteration=0,
        session_type="loop",
    )

    worker_settings = None
    prover_worker_settings = None
    prover_statement_worker_settings = None
    formalize_worker_settings = None
    repair_worker_settings = None
    main_theorem_formalize_worker_settings = None
    main_theorem_repair_worker_settings = None
    prioritize_open_problems_worker_settings = None
    if not args.enable_worker:
        raise ValueError(
            "run_loop.py now requires --enable-worker. "
            "Use a contract-compatible worker command such as scripts/codex_worker.py or scripts/mock_worker.py."
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
    main_theorem_formalize_worker_settings = load_task_worker_settings(
        task_name="formalize",
        base_settings=worker_settings,
        timeout_override=args.main_theorem_formalize_worker_timeout,
    )
    main_theorem_repair_worker_settings = load_task_worker_settings(
        task_name="repair",
        base_settings=worker_settings,
        timeout_override=args.main_theorem_repair_worker_timeout,
    )
    prioritize_open_problems_worker_settings = load_task_worker_settings(
        task_name="prioritize_open_problems",
        base_settings=worker_settings,
    )
    completed_iterations = 0
    last_priority_refresh_theorem_count = 0
    archived_path = data_dir / ARCHIVED_PROBLEMS_FILENAME
    next_main_theorem_check_count = next_main_theorem_trigger_count(
        len(derived_entries),
        args.main_theorem_interval,
    )
    while True:
        if not open_path.exists() and not archived_path.exists():
            run_status = "open_problems_missing"
            finalize_run_summary(
                artifact_paths["summary"],
                run_id=run_id,
                started_at=run_started_at,
                started_monotonic=run_started_monotonic,
                metrics=compile_metrics,
                status=run_status,
            )
            print({"status": "open_problems_missing", "iterations_completed": completed_iterations})
            return

        open_rows = [normalize_open_problem_row(row) for row in read_jsonl(open_path)]
        archived_rows = read_archived_problem_rows(data_dir)
        tracked_rows = open_rows + archived_rows
        if not tracked_rows:
            run_status = "no_open_problems"
            finalize_run_summary(
                artifact_paths["summary"],
                run_id=run_id,
                started_at=run_started_at,
                started_monotonic=run_started_monotonic,
                metrics=compile_metrics,
                status=run_status,
            )
            print({"status": "no_open_problems", "iterations_completed": completed_iterations, "archived_problem_count": 0})
            return

        if completed_iterations == 0 and not any(open_problem_priority_label(row) == "unknown" for row in tracked_rows):
            last_priority_refresh_theorem_count = len(derived_entries)

        if args.max_iterations is not None and completed_iterations >= args.max_iterations:
            run_status = "max_iterations_reached"
            finalize_run_summary(
                artifact_paths["summary"],
                run_id=run_id,
                started_at=run_started_at,
                started_monotonic=run_started_monotonic,
                metrics=compile_metrics,
                status=run_status,
            )
            print({"status": "max_iterations_reached", "iterations_completed": completed_iterations})
            return

        iteration_num = completed_iterations + 1
        derived_theorem_count = len(derived_entries)
        priority_refresh_ran = False
        priority_refresh_error = ""
        priority_refresh_worker_meta: dict[str, Any] = {}

        if (
            prioritize_open_problems_worker_settings is not None
            and should_refresh_open_problem_priorities(
                tracked_rows,
                derived_theorem_count=derived_theorem_count,
                last_refresh_theorem_count=last_priority_refresh_theorem_count,
                refresh_interval=args.priority_refresh_theorem_interval,
            )
        ):
            emit_phase_log(
                args.phase_logs,
                "open_problem_priority_refresh",
                iteration=iteration_num,
                tracked_problem_count=len(tracked_rows),
                derived_theorem_count=derived_theorem_count,
            )
            prioritizer_prompt = load_prompt_text(args.prioritize_open_problems_prompt_file)
            try:
                priority_updates, priority_refresh_worker_meta = request_open_problem_priorities(
                    worker_settings=prioritize_open_problems_worker_settings,
                    prioritizer_prompt=prioritizer_prompt,
                    tracked_rows=tracked_rows,
                    derived_entries=derived_entries,
                    current_iteration=iteration_num,
                )
                tracked_rows = apply_open_problem_priorities(
                    tracked_rows,
                    priority_updates,
                )
                last_priority_refresh_theorem_count = derived_theorem_count
                priority_refresh_ran = True
            except (RuntimeError, ValueError) as exc:
                priority_refresh_error = str(exc)
                debug_log(f"Open problem priority refresh failed: {exc}")
                emit_phase_log(
                    args.phase_logs,
                    "open_problem_priority_refresh_error",
                    iteration=iteration_num,
                    error=str(exc),
                )

        next_open_rows, next_archived_rows = split_active_and_archived_problem_queues(
            tracked_rows,
            failure_archive_threshold=args.open_problem_failure_threshold,
        )
        queue_changed = next_open_rows != open_rows or next_archived_rows != archived_rows
        open_rows = next_open_rows
        archived_rows = next_archived_rows

        if queue_changed or priority_refresh_ran:
            write_jsonl_atomic(open_path, open_rows)
            write_jsonl_atomic(archived_path, archived_rows)

        if not open_rows:
            run_status = "no_open_problems"
            finalize_run_summary(
                artifact_paths["summary"],
                run_id=run_id,
                started_at=run_started_at,
                started_monotonic=run_started_monotonic,
                metrics=compile_metrics,
                status=run_status,
            )
            print(
                {
                    "status": "no_open_problems",
                    "iterations_completed": completed_iterations,
                    "archived_problem_count": len(archived_rows),
                }
            )
            return

        debug_log(f"=== Iteration {iteration_num} START ===")
        debug_log(f"{len(open_rows)} active problems in queue")
        debug_log(f"{len(archived_rows)} archived problems kept for priority context")

        emit_phase_log(
            args.phase_logs,
            "iteration_start",
            iteration=completed_iterations + 1,
            open_problem_count=len(open_rows),
            archived_problem_count=len(archived_rows),
        )

        # Select problem using local deterministic logic, no LLM needed
        debug_log(f"Selecting problem locally from {len(open_rows)} queued problems")
        picked = pick_next_problem(open_rows)

        if picked is None:
            run_status = "no_open_problems"
            finalize_run_summary(
                artifact_paths["summary"],
                run_id=run_id,
                started_at=run_started_at,
                started_monotonic=run_started_monotonic,
                metrics=compile_metrics,
                status=run_status,
            )
            print(
                {
                    "status": "no_open_problems",
                    "iterations_completed": completed_iterations,
                    "archived_problem_count": len(archived_rows),
                }
            )
            return

        problem_id = str(picked["id"])
        original_stmt = str(picked.get("stmt", ""))
        initial_theory_context = build_problem_theory_context(base_theory_context, derived_entries, original_stmt)
        emit_phase_log(args.phase_logs, "problem_selected", iteration=completed_iterations + 1, problem_id=problem_id)

        current_iteration_full_logs: list[dict[str, Any]] = []
        (
            solver_stmt,
            statement_formalization_result,
            theorem_name_stem,
            docstring_summary,
            statement_formalization_notes,
            prover_statement_worker_meta,
        ) = resolve_solver_statement(
            prover_statement_worker_settings=prover_statement_worker_settings,
            prover_statement_prompt_file=args.prover_statement_prompt_file,
            phase_logs=args.phase_logs,
            iteration=completed_iterations + 1,
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
                "new_problems": [],
            },
        )
        same_problem_history_tail = load_formalization_memory(memory_path, problem_id)[-8:]

        theory_context = build_problem_theory_context(
            base_theory_context,
            derived_entries,
            target_stmt,
        )

        prover_attempts_used = 1
        proof_sketch = ""
        proof_text = ""
        counterexample_text = ""
        prover_worker_meta: dict[str, Any] = {}
        new_problems: list[str] = []
        if not solver_stmt:
            result = "stuck"
            proof_sketch = statement_formalization_notes or "Statement formalization failed before proof search."
            counterexample_text = ""
            new_problems = []
        else:
            emit_phase_log(args.phase_logs, "prover", iteration=completed_iterations + 1, problem_id=problem_id, mode="worker")
            prover_prompt = load_prompt_text(args.prover_prompt_file)
            result, proof_sketch, counterexample_text, new_problems, prover_attempts_used, prover_worker_meta = query_prover_with_retries(
                worker_settings=prover_worker_settings,
                prover_prompt=prover_prompt,
                problem_id=problem_id,
                stmt=solver_stmt,
                original_stmt=original_stmt,
                open_rows=open_rows,
                prover_retries=args.prover_retries,
                theory_context=theory_context,
                memory_path=memory_path,
                current_iteration_full_logs=current_iteration_full_logs,
                same_problem_history_tail=same_problem_history_tail,
                run_id=run_id,
                session_type="loop",
                iteration=completed_iterations + 1,
                phase_attempts_path=artifact_paths["phase_attempts"],
            )
            emit_parse_phase_log(
                args.phase_logs,
                "worker_parse",
                iteration=completed_iterations + 1,
                problem_id=problem_id,
                worker_meta=prover_worker_meta,
            )

        formalizer_prompt = load_prompt_text(args.formalizer_prompt_file) if formalize_worker_settings is not None else ""
        repair_prompt_file = args.repair_prompt_file or args.formalizer_prompt_file
        repair_prompt = load_prompt_text(repair_prompt_file) if repair_worker_settings is not None else ""
        theorem_code = ""
        (
            verify_success,
            theorem_name,
            result,
            proof_text,
            counterexample_text,
            new_problems,
            verify_error_excerpt,
            target_stmt,
        ) = attempt_formalization_until_timeout(
            problem_id=problem_id,
            theorem_name=theorem_name or build_theorem_name(problem_id, "statement_target"),
            stmt=target_stmt,
            result=result,
            proof_sketch=proof_sketch,
            counterexample_text=counterexample_text,
            new_problems=new_problems,
            scratch_file=scratch_file,
            skip_verify=args.skip_verify,
            formalize_worker_settings=formalize_worker_settings,
            repair_worker_settings=repair_worker_settings,
            formalizer_prompt=formalizer_prompt,
            repair_prompt=repair_prompt,
            open_rows=open_rows,
            theory_context=theory_context,
            verify_timeout_sec=180,
            formalization_retry_budget_sec=args.formalization_retry_budget_sec,
            memory_path=memory_path,
            current_iteration_full_logs=current_iteration_full_logs,
            initial_proof_text=proof_text,
            phase_logger=(lambda **fields: emit_phase_log(args.phase_logs, iteration=completed_iterations + 1, **fields)),
            run_id=run_id,
            session_type="loop",
            iteration=completed_iterations + 1,
            phase_attempts_path=artifact_paths["phase_attempts"],
            compile_metrics=compile_metrics,
        )
        if verify_success and result in {"proof", "counterexample"}:
            derived_count_before_append = len(derived_entries)
            theorem_code = append_verified_theorem_from_scratch(
                scratch_path=scratch_file,
                derived_file=Path(args.derived_file),
                derived_entries=derived_entries,
                docstring=build_theorem_docstring(
                    problem_id=problem_id,
                    docstring_summary=docstring_summary,
                    theorem_name_stem=theorem_name_stem,
                    statement_formalization_notes=statement_formalization_notes,
                ),
            )
            theorem_appended = len(derived_entries) > derived_count_before_append
            if theorem_appended:
                theory_context = build_problem_theory_context(base_theory_context, derived_entries, target_stmt)
        else:
            theorem_appended = False

        solver_new_problem_suggestions = list(new_problems)
        expander_new_problem_suggestions: list[str] = []
        expander_worker_meta: dict[str, Any] = {}
        expand_target_stmt = target_stmt

        new_problems = list(solver_new_problem_suggestions)

        if worker_settings is not None:
            emit_phase_log(
                args.phase_logs,
                "expand_generate",
                iteration=completed_iterations + 1,
                problem_id=problem_id,
                mode="worker",
            )
            expand_prompt = load_prompt_text(args.expander_prompt_file)
            same_problem_history_tail = load_formalization_memory(memory_path, problem_id)[-8:]
            expand_started_monotonic = time.monotonic()
            expand_started_at = iso_timestamp_now()
            try:
                expander_candidates, expander_worker_meta = request_expand_candidates(
                    worker_settings=worker_settings,
                    expand_prompt=expand_prompt,
                    task_type="expand",
                    problem_id=problem_id,
                    stmt=expand_target_stmt,
                    original_stmt=original_stmt,
                    result=result,
                    verify_success=verify_success,
                    theory_context=theory_context,
                    open_rows=open_rows,
                    existing_new_problems=solver_new_problem_suggestions,
                    verify_error_excerpt=verify_error_excerpt,
                    current_iteration_full_logs=current_iteration_full_logs,
                    same_problem_history_tail=same_problem_history_tail,
                    max_candidates=2,
                )
                append_phase_attempt_record(
                    artifact_paths["phase_attempts"],
                    run_id=run_id,
                    session_type="loop",
                    iteration=completed_iterations + 1,
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
                    iteration=completed_iterations + 1,
                    problem_id=problem_id,
                    generated_count=len(expander_candidates),
                )
                expander_new_problem_suggestions = [item["statement"] for item in expander_candidates]
                new_problems = merge_new_problems(new_problems, expander_new_problem_suggestions, max_items=2)
            except (RuntimeError, ValueError) as exc:
                append_phase_attempt_record(
                    artifact_paths["phase_attempts"],
                    run_id=run_id,
                    session_type="loop",
                    iteration=completed_iterations + 1,
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
                debug_log(f"Expander failed for {problem_id}: {exc}")
                emit_phase_log(
                    args.phase_logs,
                    "expand_generate_error",
                    iteration=completed_iterations + 1,
                    problem_id=problem_id,
                    error=str(exc),
                )

        report = apply_state_update(
            data_dir=data_dir,
            problem_id=problem_id,
            result=result,
            verify_success=verify_success,
            theorem_name=theorem_name,
            new_problems=new_problems,
            source_details={
                "parent_entity_id": problem_id,
                "parent_entity_type": "open_problem",
                "generated_by_phase": "expand",
                "created_at_run_id": run_id,
                "created_at_iteration": completed_iterations + 1,
                "created_in_session_type": "loop",
            },
            result_metadata={
                "run_id": run_id,
                "iteration": completed_iterations + 1,
                "session_type": "loop",
            },
            failure_threshold=args.open_problem_failure_threshold,
            current_iteration=completed_iterations + 1,
        )
        current_iteration = completed_iterations + 1
        record_problem_rows(
            list(report.get("added_problem_rows", [])),
            iteration=current_iteration,
            session_type="loop",
        )
        for added_row in list(report.get("added_problem_rows", [])):
            added_problem_id = str(added_row.get("id", "")).strip()
            if added_problem_id:
                append_lineage_edge_record(
                    artifact_paths["lineage_edges"],
                    run_id=run_id,
                    iteration=current_iteration,
                    session_type="loop",
                    parent_id=problem_id,
                    child_id=added_problem_id,
                    edge_type="generated_from",
                )
        if theorem_appended and theorem_name and result == "proof":
            compile_metrics["solved_per_run"] += 1
            elapsed_ms = monotonic_duration_ms(run_started_monotonic)
            if compile_metrics["time_to_first_green_ms"] is None:
                compile_metrics["time_to_first_green_ms"] = elapsed_ms
            compile_metrics["wall_clock_to_last_solve_ms"] = elapsed_ms
            record_theorem(
                theorem_name,
                target_stmt,
                iteration=current_iteration,
                session_type="loop",
            )
            append_lineage_edge_record(
                artifact_paths["lineage_edges"],
                run_id=run_id,
                iteration=current_iteration,
                session_type="loop",
                parent_id=problem_id,
                child_id=theorem_name,
                edge_type="solved_as",
            )
        emit_phase_log(args.phase_logs, "state_update", iteration=completed_iterations + 1, problem_id=problem_id)
        completed_iterations += 1
        debug_log(f"=== Iteration {completed_iterations} END ({result}, verify={verify_success}) ===\n")
        report["picked_problem_id"] = problem_id
        report["picked_problem_priority"] = open_problem_priority_label(picked)
        report["result"] = result
        report["verify_success"] = verify_success
        report["verify_error_excerpt"] = verify_error_excerpt
        report["original_stmt"] = original_stmt
        report["formalized_stmt"] = target_stmt if solver_stmt else ""
        report["prover_statement_result"] = statement_formalization_result
        report["prover_attempts_used"] = prover_attempts_used
        report["final_new_problems"] = new_problems
        report["priority_refresh_ran"] = priority_refresh_ran
        report["priority_refresh_error"] = priority_refresh_error
        auto_main_theorem_report: dict[str, Any] | None = None
        if (
            worker_settings is not None
            and theorem_appended
            and next_main_theorem_check_count is not None
            and len(derived_entries) >= next_main_theorem_check_count
        ):
            emit_phase_log(
                args.phase_logs,
                "main_theorem_interval_reached",
                iteration=completed_iterations,
                derived_theorem_count=len(derived_entries),
                threshold=next_main_theorem_check_count,
            )
            auto_main_theorem_report = run_manual_main_theorem_check(
                worker_settings=worker_settings,
                scratch_file=scratch_file,
                derived_file=derived_path,
                derived_entries=derived_entries,
                data_dir=data_dir,
                base_theory_context=base_theory_context,
                formalization_memory_path=memory_path,
                formalize_worker_settings=main_theorem_formalize_worker_settings,
                repair_worker_settings=main_theorem_repair_worker_settings,
                formalizer_prompt_file=args.formalizer_prompt_file,
                repair_prompt_file=repair_prompt_file,
                suggest_prompt_file=args.main_theorem_suggest_prompt_file,
                plan_prompt_file=args.main_theorem_plan_prompt_file,
                post_expand_prompt_file=args.main_theorem_post_expand_prompt_file,
                prioritize_open_problems_worker_settings=prioritize_open_problems_worker_settings,
                prioritize_open_problems_prompt_file=args.prioritize_open_problems_prompt_file,
                current_iteration=completed_iterations,
                skip_verify=args.skip_verify,
                verify_timeout_sec=(
                    None
                    if args.main_theorem_verify_timeout == 0
                    else args.main_theorem_verify_timeout
                ),
                formalization_retry_budget_sec=(
                    None
                    if args.main_theorem_formalization_retry_budget_sec == 0
                    else args.main_theorem_formalization_retry_budget_sec
                ),
                max_repair_rounds=20,
                max_same_error_streak=5,
                post_expand_count=5,
                failure_threshold=args.open_problem_failure_threshold,
                phase_logs=args.phase_logs,
                run_id=run_id,
                phase_attempts_path=artifact_paths["phase_attempts"],
                compile_metrics=compile_metrics,
            )
            if auto_main_theorem_report is not None:
                main_theorem_name = str(auto_main_theorem_report.get("theorem_name", "")).strip()
                main_candidate_id = str(auto_main_theorem_report.get("candidate_id", "")).strip()
                if bool(auto_main_theorem_report.get("verify_success", False)) and main_theorem_name:
                    record_theorem(
                        main_theorem_name,
                        str(auto_main_theorem_report.get("statement", "")),
                        iteration=completed_iterations,
                        session_type="main_theorem_session",
                    )
                    if main_candidate_id:
                        append_lineage_edge_record(
                            artifact_paths["lineage_edges"],
                            run_id=run_id,
                            iteration=completed_iterations,
                            session_type="main_theorem_session",
                            parent_id=main_candidate_id,
                            child_id=main_theorem_name,
                            edge_type="proved_as_main",
                        )
                    for supporting_theorem in list(auto_main_theorem_report.get("supporting_theorems", [])):
                        supporting_name = str(supporting_theorem).strip()
                        if not supporting_name or not main_candidate_id:
                            continue
                        append_lineage_edge_record(
                            artifact_paths["lineage_edges"],
                            run_id=run_id,
                            iteration=completed_iterations,
                            session_type="main_theorem_session",
                            parent_id=supporting_name,
                            child_id=main_candidate_id,
                            edge_type="selected_as_main",
                        )
                added_problem_rows = list(auto_main_theorem_report.get("enqueue_added_problem_rows", []))
                record_problem_rows(
                    added_problem_rows,
                    iteration=completed_iterations,
                    session_type="main_theorem_session",
                )
                for added_row in added_problem_rows:
                    added_problem_id = str(added_row.get("id", "")).strip()
                    if added_problem_id and main_theorem_name:
                        append_lineage_edge_record(
                            artifact_paths["lineage_edges"],
                            run_id=run_id,
                            iteration=completed_iterations,
                            session_type="main_theorem_session",
                            parent_id=main_theorem_name,
                            child_id=added_problem_id,
                            edge_type="post_theorem_expand",
                        )
            emit_phase_log(
                args.phase_logs,
                "main_theorem_interval_result",
                iteration=completed_iterations,
                status=str(auto_main_theorem_report.get("status", "")),
                verify_success=bool(auto_main_theorem_report.get("verify_success", False)),
                processed=bool(auto_main_theorem_report.get("processed", False)),
            )
            next_main_theorem_check_count = next_main_theorem_trigger_count(
                len(derived_entries),
                args.main_theorem_interval,
            )
        report["auto_main_theorem_triggered"] = auto_main_theorem_report is not None
        report["auto_main_theorem_report"] = auto_main_theorem_report
        report["next_main_theorem_trigger_count"] = next_main_theorem_check_count
        final_open_rows = [normalize_open_problem_row(row) for row in read_jsonl(open_path)]
        final_archived_rows = read_archived_problem_rows(data_dir)
        report["archived_problem_count"] = len(final_archived_rows)
        report["active_open_problem_count"] = len(final_open_rows)
        report["iteration"] = completed_iterations
        print(report)


if __name__ == "__main__":
    main()
