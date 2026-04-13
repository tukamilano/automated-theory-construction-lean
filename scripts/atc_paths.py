from __future__ import annotations

from pathlib import Path


DATA_ROOT = Path("data")
LOOP_DIRNAME = "loop"
PAPER_CLAIM_DIRNAME = "paper_claim"
REFRACTOR_DIRNAME = "refactor"
RUNS_DIRNAME = "runs"
MATERIALS_CACHE_DIRNAME = "materials_cache"

OPEN_PROBLEMS_FILENAME = "open_problems.jsonl"
ARCHIVED_PROBLEMS_FILENAME = "archived_problems.jsonl"
SOLVED_PROBLEMS_FILENAME = "solved_problems.jsonl"
COUNTEREXAMPLES_FILENAME = "counterexamples.jsonl"
THEORY_STATE_FILENAME = "theory_state.json"
FORMALIZATION_MEMORY_FILENAME = "formalization_memory.json"
THEOREM_REUSE_MEMORY_FILENAME = "theorem_reuse_memory.json"
PAPER_CLAIM_REJECTION_MEMORY_FILENAME = "paper_claim_rejection_memory.json"
EXPAND_CANDIDATES_FILENAME = "expand_candidates.jsonl"
PAPER_CLAIM_EVENTS_FILENAME = "paper_claim.events.jsonl"
PAPER_CLAIM_REPORT_FILENAME = "paper_claim.report.json"

REFACTOR_PREVIEW_FILENAME = "Derived.refactored.preview.lean"
REFACTOR_REVIEWED_FILENAME = "Derived.refactored.reviewed.lean"
REFACTOR_REVIEW_REPORT_FILENAME = "Derived.refactored.reviewed.report.json"
REFACTOR_TRY_AT_EACH_STEP_RAW_FILENAME = "Derived.tryAtEachStep.json"
REFACTOR_TRY_AT_EACH_STEP_APPLY_REPORT_FILENAME = "Derived.tryAtEachStep.apply_report.json"
REFACTOR_DEPS_FILENAME = "derived-deps.json"
REFACTOR_CHUNK_PLAN_FILENAME = "derived-chunk-plan.json"


def loop_data_dir(data_dir: Path) -> Path:
    return data_dir if data_dir.name == LOOP_DIRNAME else data_dir / LOOP_DIRNAME


def paper_claim_data_dir(data_dir: Path) -> Path:
    return data_dir if data_dir.name == PAPER_CLAIM_DIRNAME else data_dir / PAPER_CLAIM_DIRNAME


def refactor_data_dir(data_dir: Path) -> Path:
    return data_dir if data_dir.name == REFRACTOR_DIRNAME else data_dir / REFRACTOR_DIRNAME


def loop_open_problems_path(data_dir: Path) -> Path:
    return loop_data_dir(data_dir) / OPEN_PROBLEMS_FILENAME


def loop_archived_problems_path(data_dir: Path) -> Path:
    return loop_data_dir(data_dir) / ARCHIVED_PROBLEMS_FILENAME


def loop_solved_problems_path(data_dir: Path) -> Path:
    return loop_data_dir(data_dir) / SOLVED_PROBLEMS_FILENAME


def loop_counterexamples_path(data_dir: Path) -> Path:
    return loop_data_dir(data_dir) / COUNTEREXAMPLES_FILENAME


def loop_theory_state_path(data_dir: Path) -> Path:
    return loop_data_dir(data_dir) / THEORY_STATE_FILENAME


def loop_formalization_memory_path(data_dir: Path) -> Path:
    return loop_data_dir(data_dir) / FORMALIZATION_MEMORY_FILENAME


def loop_theorem_reuse_memory_path(data_dir: Path) -> Path:
    return loop_data_dir(data_dir) / THEOREM_REUSE_MEMORY_FILENAME


def loop_paper_claim_rejection_memory_path(data_dir: Path) -> Path:
    return loop_data_dir(data_dir) / PAPER_CLAIM_REJECTION_MEMORY_FILENAME


def loop_expand_candidates_path(data_dir: Path) -> Path:
    return loop_data_dir(data_dir) / EXPAND_CANDIDATES_FILENAME


def refactor_preview_path(data_dir: Path) -> Path:
    return refactor_data_dir(data_dir) / REFACTOR_PREVIEW_FILENAME


def refactor_reviewed_path(data_dir: Path) -> Path:
    return refactor_data_dir(data_dir) / REFACTOR_REVIEWED_FILENAME


def refactor_review_report_path(data_dir: Path) -> Path:
    return refactor_data_dir(data_dir) / REFACTOR_REVIEW_REPORT_FILENAME


def refactor_try_at_each_step_raw_output_path(data_dir: Path) -> Path:
    return refactor_data_dir(data_dir) / REFACTOR_TRY_AT_EACH_STEP_RAW_FILENAME


def refactor_try_at_each_step_apply_report_path(data_dir: Path) -> Path:
    return refactor_data_dir(data_dir) / REFACTOR_TRY_AT_EACH_STEP_APPLY_REPORT_FILENAME


def refactor_deps_path(data_dir: Path) -> Path:
    return refactor_data_dir(data_dir) / REFACTOR_DEPS_FILENAME


def refactor_chunk_plan_path(data_dir: Path) -> Path:
    return refactor_data_dir(data_dir) / REFACTOR_CHUNK_PLAN_FILENAME


def paper_claim_run_dir(data_dir: Path, run_id: str) -> Path:
    return paper_claim_data_dir(data_dir) / run_id


def paper_claim_session_events_path(data_dir: Path, run_id: str) -> Path:
    return paper_claim_run_dir(data_dir, run_id) / PAPER_CLAIM_EVENTS_FILENAME


def paper_claim_report_path(data_dir: Path, run_id: str) -> Path:
    return paper_claim_run_dir(data_dir, run_id) / PAPER_CLAIM_REPORT_FILENAME
