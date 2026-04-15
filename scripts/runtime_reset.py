from __future__ import annotations

from collections.abc import Callable
from pathlib import Path
import shutil
from typing import Any

from atc_paths import loop_counterexamples_path
from atc_paths import loop_data_dir
from atc_paths import loop_expand_candidates_path
from atc_paths import loop_open_problems_path
from atc_paths import loop_paper_claim_rejection_memory_path
from atc_paths import loop_solved_problems_path
from atc_paths import loop_theorem_reuse_memory_path
from atc_paths import loop_theory_state_path
from atc_paths import paper_claim_data_dir
from atc_paths import refactor_data_dir
from common import LEGACY_DEFERRED_PROBLEMS_FILENAME
from common import LEGACY_PRUNED_OPEN_PROBLEMS_FILENAME
from common import write_jsonl_atomic
def _clear_directory_contents(root: Path) -> None:
    root.mkdir(parents=True, exist_ok=True)
    for path in root.iterdir():
        if path.is_dir():
            shutil.rmtree(path)
        else:
            path.unlink(missing_ok=True)


def reset_loop_runtime_data(
    *,
    data_dir: Path,
    derived_file: Path,
    open_problem_rows: list[dict[str, Any]],
    archived_problems_file: Path,
    clear_paper_claim_rejection_memory: bool,
) -> None:
    loop_dir = loop_data_dir(data_dir)
    loop_dir.mkdir(parents=True, exist_ok=True)
    _clear_directory_contents(paper_claim_data_dir(data_dir))
    _clear_directory_contents(refactor_data_dir(data_dir))
    shutil.rmtree(derived_file.parent / "Generated", ignore_errors=True)
    write_jsonl_atomic(loop_open_problems_path(data_dir), open_problem_rows)
    write_jsonl_atomic(archived_problems_file, [])
    write_jsonl_atomic(loop_solved_problems_path(data_dir), [])
    write_jsonl_atomic(loop_counterexamples_path(data_dir), [])
    loop_theorem_reuse_memory_path(data_dir).write_text('{"entries": []}\n', encoding="utf-8")
    if clear_paper_claim_rejection_memory:
        loop_paper_claim_rejection_memory_path(data_dir).write_text('{"entries": []}\n', encoding="utf-8")
    loop_expand_candidates_path(data_dir).unlink(missing_ok=True)
    (loop_dir / LEGACY_DEFERRED_PROBLEMS_FILENAME).unlink(missing_ok=True)
    (loop_dir / LEGACY_PRUNED_OPEN_PROBLEMS_FILENAME).unlink(missing_ok=True)
    loop_theory_state_path(data_dir).unlink(missing_ok=True)


def reset_loop_work_files(
    *,
    scratch_file: Path,
    cleanup_parallel_scratch_files: Callable[[Path], None],
    reset_scratch: bool,
    scratch_template: str,
    derived_file: Path,
    derived_cleanup_files: tuple[Path, ...],
    reset_derived: bool,
    derived_template: str,
    formalization_memory_file: Path,
    reset_formalization_memory: bool,
) -> None:
    cleanup_parallel_scratch_files(scratch_file)

    if reset_scratch:
        scratch_file.parent.mkdir(parents=True, exist_ok=True)
        scratch_file.write_text(scratch_template, encoding="utf-8")

    if reset_derived:
        derived_file.parent.mkdir(parents=True, exist_ok=True)
        derived_file.write_text(derived_template, encoding="utf-8")
        for cleanup_file in derived_cleanup_files:
            cleanup_file.unlink(missing_ok=True)

    if reset_formalization_memory:
        formalization_memory_file.parent.mkdir(parents=True, exist_ok=True)
        formalization_memory_file.write_text("{}\n", encoding="utf-8")
