from __future__ import annotations

import argparse
from pathlib import Path

from run_loop import (
    extract_derived_theorem_entries,
    load_optional_text,
    load_task_worker_settings,
    load_worker_settings,
    run_manual_main_theorem_check,
)


def main() -> None:
    parser = argparse.ArgumentParser(description="Run a one-shot manual main-theorem check.")
    parser.add_argument("--enable-worker", action="store_true")
    parser.add_argument("--worker-command")
    parser.add_argument("--worker-timeout", type=int)
    parser.add_argument("--skip-verify", action="store_true")
    parser.add_argument("--open-problem-failure-threshold", type=int, default=2)
    args = parser.parse_args()

    if args.open_problem_failure_threshold < 0:
        raise ValueError("--open-problem-failure-threshold must be >= 0")

    data_dir = Path("data")
    scratch_file = Path("AutomatedTheoryConstruction/Scratch.lean")
    derived_file = Path("AutomatedTheoryConstruction/Derived.lean")
    memory_path = Path("data/formalization_memory.json")
    base_theory_context = load_optional_text("AutomatedTheoryConstruction/Theory.lean")
    derived_entries = extract_derived_theorem_entries(derived_file)

    worker_settings = None
    formalize_worker_settings = None
    repair_worker_settings = None
    prioritize_open_problems_worker_settings = None
    if args.enable_worker:
        worker_settings = load_worker_settings(
            command_override=args.worker_command,
            timeout_override=args.worker_timeout,
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

    report = run_manual_main_theorem_check(
        worker_settings=worker_settings,
        scratch_file=scratch_file,
        derived_file=derived_file,
        derived_entries=derived_entries,
        data_dir=data_dir,
        base_theory_context=base_theory_context,
        formalization_memory_path=memory_path,
        formalize_worker_settings=formalize_worker_settings,
        repair_worker_settings=repair_worker_settings,
        formalizer_prompt_file="prompts/formalizer_simple.md",
        repair_prompt_file="prompts/formalizer_simple.md",
        suggest_prompt_file="prompts/main_theorem_suggester.md",
        plan_prompt_file="prompts/main_theorem_planner.md",
        post_expand_prompt_file="prompts/post_theorem_expander.md",
        prioritize_open_problems_worker_settings=prioritize_open_problems_worker_settings,
        prioritize_open_problems_prompt_file="prompts/open_problem_prioritizer.md",
        current_iteration=0,
        skip_verify=args.skip_verify,
        verify_timeout_sec=180,
        formalization_retry_budget_sec=900,
        max_repair_rounds=20,
        max_same_error_streak=5,
        post_expand_count=5,
        failure_threshold=args.open_problem_failure_threshold,
        phase_logs=True,
    )
    print(report)


if __name__ == "__main__":
    main()
