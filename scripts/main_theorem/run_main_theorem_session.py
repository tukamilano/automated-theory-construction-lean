from __future__ import annotations

import argparse
import json
import os
import sys
import threading
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
SCRIPTS_ROOT = SCRIPT_DIR.parent
LOOP_ROOT = SCRIPTS_ROOT / "loop"
REPO_ROOT = SCRIPTS_ROOT.parent
for search_path in (SCRIPTS_ROOT, LOOP_ROOT):
    search_path_str = str(search_path)
    if search_path_str not in sys.path:
        sys.path.insert(0, search_path_str)

from common import load_theory_context
from derived_entries import extract_derived_theorem_entries
from main_theorem_session import run_main_theorem_session
from worker_client import load_task_worker_settings
from worker_client import load_worker_settings


def main() -> None:
    parser = argparse.ArgumentParser(description="Run a one-shot main theorem session.")
    worker_timeout_help = "Per worker subprocess timeout in seconds."
    verify_timeout_help = "Per Lean verification timeout in seconds."
    retry_budget_help = "Whole retry-loop budget in seconds."
    parser.add_argument("--theory-file", default="AutomatedTheoryConstruction/Theory.lean")
    parser.add_argument("--derived-file", default="AutomatedTheoryConstruction/Derived.lean")
    parser.add_argument("--scratch-file", default="AutomatedTheoryConstruction/Scratch.lean")
    parser.add_argument("--data-dir", default="data")
    parser.add_argument("--formalization-memory-file", default="data/formalization_memory.json")
    parser.add_argument("--phase-attempts-file")
    parser.add_argument("--session-events-file")
    parser.add_argument("--report-file")
    parser.add_argument("--run-id", default="main-theorem-session")
    parser.add_argument("--current-iteration", type=int, default=0)
    parser.add_argument("--phase-logs", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--enable-worker", action="store_true")
    parser.add_argument("--worker-command")
    parser.add_argument("--worker-timeout", type=int, help=worker_timeout_help)
    parser.add_argument("--formalize-worker-timeout", type=int, help=worker_timeout_help)
    parser.add_argument("--repair-worker-timeout", type=int, help=worker_timeout_help)
    parser.add_argument("--prioritize-open-problems-worker-timeout", type=int, help=worker_timeout_help)
    parser.add_argument("--skip-verify", action="store_true")
    parser.add_argument("--verify-timeout", type=int, default=600, help=verify_timeout_help)
    parser.add_argument("--formalization-retry-budget-sec", type=int, default=3600, help=retry_budget_help)
    parser.add_argument("--max-same-error-streak", type=int, default=5)
    parser.add_argument("--open-problem-failure-threshold", type=int, default=2)
    parser.add_argument("--batch-generator-seed-count", type=int, default=4)
    parser.add_argument("--batch-generator-open-target-min", type=int, default=2)
    args = parser.parse_args()

    if args.current_iteration < 0:
        raise ValueError("--current-iteration must be >= 0")
    if args.open_problem_failure_threshold < 0:
        raise ValueError("--open-problem-failure-threshold must be >= 0")
    if args.verify_timeout < 0:
        raise ValueError("--verify-timeout must be >= 0")
    if args.formalization_retry_budget_sec < 0:
        raise ValueError("--formalization-retry-budget-sec must be >= 0")
    if args.max_same_error_streak < 1:
        raise ValueError("--max-same-error-streak must be >= 1")
    if args.batch_generator_seed_count < 0:
        raise ValueError("--batch-generator-seed-count must be >= 0")
    if args.batch_generator_open_target_min < 0:
        raise ValueError("--batch-generator-open-target-min must be >= 0")

    verify_timeout_sec = None if args.verify_timeout == 0 else args.verify_timeout
    formalization_retry_budget_sec = (
        None if args.formalization_retry_budget_sec == 0 else args.formalization_retry_budget_sec
    )

    data_dir = Path(args.data_dir)
    scratch_file = Path(args.scratch_file)
    derived_file = Path(args.derived_file)
    theory_file = Path(args.theory_file)
    memory_path = Path(args.formalization_memory_file)
    phase_attempts_path = Path(args.phase_attempts_file) if args.phase_attempts_file else None
    session_events_path = (
        Path(args.session_events_file)
        if args.session_events_file
        else data_dir / "runs" / args.run_id / "main_theorem.events.jsonl"
    )
    _, base_theory_context = load_theory_context(theory_file)
    derived_entries = extract_derived_theorem_entries(derived_file)

    worker_settings = None
    formalize_worker_settings = None
    repair_worker_settings = None
    prioritize_open_problems_worker_settings = None
    if args.enable_worker:
        if args.worker_timeout == 0:
            os.environ["ATC_WORKER_TIMEOUT"] = "0"
        if args.formalize_worker_timeout == 0:
            os.environ["ATC_FORMALIZE_WORKER_TIMEOUT"] = "0"
        if args.repair_worker_timeout == 0:
            os.environ["ATC_REPAIR_WORKER_TIMEOUT"] = "0"
        worker_settings = load_worker_settings(
            command_override=args.worker_command,
            timeout_override=args.worker_timeout,
        )
        formalize_worker_settings = load_task_worker_settings(
            task_name="formalize",
            base_settings=worker_settings,
            timeout_override=args.formalize_worker_timeout,
            codex_timeout_override=args.formalize_worker_timeout,
        )
        repair_worker_settings = load_task_worker_settings(
            task_name="repair",
            base_settings=worker_settings,
            timeout_override=args.repair_worker_timeout,
            codex_timeout_override=args.repair_worker_timeout,
        )
        prioritize_open_problems_worker_settings = load_task_worker_settings(
            task_name="prioritize_open_problems",
            base_settings=worker_settings,
            timeout_override=args.prioritize_open_problems_worker_timeout,
            codex_timeout_override=args.prioritize_open_problems_worker_timeout,
        )

    report = run_main_theorem_session(
        worker_settings=worker_settings,
        scratch_file=scratch_file,
        derived_file=derived_file,
        derived_entries=derived_entries,
        data_dir=data_dir,
        base_theory_context=base_theory_context,
        formalization_memory_path=memory_path,
        formalize_worker_settings=formalize_worker_settings,
        repair_worker_settings=repair_worker_settings,
        formalizer_prompt_file="prompts/formalize/formalizer_proof.md",
        repair_prompt_file="prompts/formalize/repair_proof.md",
        generate_prompt_file="prompts/main_theorem/generate.md",
        select_prompt_file="prompts/main_theorem/select.md",
        post_expand_prompt_file="prompts/expander/post_theorem.md",
        prioritize_open_problems_worker_settings=prioritize_open_problems_worker_settings,
        prioritize_open_problems_prompt_file="prompts/prioritizer/open_problem_prioritizer.md",
        theory_file=theory_file,
        repo_root=REPO_ROOT,
        batch_generator_seed_count=args.batch_generator_seed_count,
        batch_generator_open_target_min=args.batch_generator_open_target_min,
        current_iteration=args.current_iteration,
        skip_verify=args.skip_verify,
        verify_timeout_sec=verify_timeout_sec,
        formalization_retry_budget_sec=formalization_retry_budget_sec,
        max_same_error_streak=args.max_same_error_streak,
        failure_threshold=args.open_problem_failure_threshold,
        phase_logs=args.phase_logs,
        run_id=args.run_id,
        phase_attempts_path=phase_attempts_path,
        session_events_path=session_events_path,
        compile_metrics={
            "compile_attempt_count": 0,
            "compile_success_count": 0,
            "solved_per_run": 0,
            "time_to_first_green_ms": None,
            "wall_clock_to_last_solve_ms": None,
        },
        state_lock=threading.Lock(),
        derived_runtime_state={"generation": 0},
    )
    report_json = json.dumps(report, ensure_ascii=False)
    if args.report_file:
        Path(args.report_file).write_text(report_json + "\n", encoding="utf-8")
    print(report_json)


if __name__ == "__main__":
    main()
