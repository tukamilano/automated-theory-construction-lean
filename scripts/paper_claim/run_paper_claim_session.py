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
from paper_claim_session import resume_paper_claim_session_from_plan_event
from paper_claim_session import run_paper_claim_session
from worker_client import load_task_worker_settings
from worker_client import load_worker_settings

PROBLEM_DESIGN_TASKS = (
    "problem_design_cluster",
    "problem_design_contextualize",
    "problem_design_core_extract",
    "paper_claim_select",
    "paper_claim_retrieve",
    "paper_claim_map",
    "paper_claim_plan",
    "paper_claim_codex_prove",
)


def _configure_problem_design_timeouts() -> None:
    for task_name in PROBLEM_DESIGN_TASKS:
        os.environ.setdefault(f"ATC_{task_name.upper()}_WORKER_TIMEOUT", "0")
        os.environ.setdefault(f"ATC_{task_name.upper()}_CODEX_TIMEOUT", "0")


def _initialize_jsonl_output(path: Path | None) -> None:
    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists():
        path.write_text("", encoding="utf-8")
        return
    try:
        if path.stat().st_size > 0:
            path.write_text("", encoding="utf-8")
    except OSError:
        path.write_text("", encoding="utf-8")


def _build_stdout_summary(report: dict[str, object], *, report_file: str | None) -> dict[str, object]:
    problem_design_dossiers = report.get("problem_design_dossiers")
    dossier_rows = problem_design_dossiers if isinstance(problem_design_dossiers, list) else []
    selected_candidate_payload = report.get("selected_candidate")
    selected_candidate = selected_candidate_payload if isinstance(selected_candidate_payload, dict) else {}
    return {
        "status": report.get("status"),
        "processed": report.get("processed"),
        "verify_success": report.get("verify_success"),
        "failed_stage": report.get("failed_stage", ""),
        "error": report.get("error", ""),
        "problem_design_dossier_count": len(dossier_rows),
        "candidate_id": selected_candidate.get("candidate_id", ""),
        "theorem_name": report.get("theorem_name", ""),
        "session_events_file": report.get("session_events_file", ""),
        "report_file": report_file or "",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Run a one-shot paper claim session.")
    worker_timeout_help = "Per worker subprocess timeout in seconds."
    verify_timeout_help = "Per Lean verification timeout in seconds."
    retry_budget_help = "Whole retry-loop budget in seconds."
    parser.add_argument("--theory-file", default="AutomatedTheoryConstruction/Theory.lean")
    parser.add_argument("--derived-file", default="AutomatedTheoryConstruction/Derived.lean")
    parser.add_argument("--scratch-file", default="AutomatedTheoryConstruction/Scratch.lean")
    parser.add_argument("--data-dir", default="data")
    parser.add_argument("--phase-attempts-file")
    parser.add_argument("--session-events-file")
    parser.add_argument("--report-file")
    parser.add_argument("--resume-from-session-events-file")
    parser.add_argument("--resume-plan-id", default="")
    parser.add_argument("--run-id", default="paper-claim-session")
    parser.add_argument("--current-iteration", type=int, default=0)
    parser.add_argument("--phase-logs", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--enable-worker", action="store_true")
    parser.add_argument("--worker-command")
    parser.add_argument("--worker-timeout", type=int, help=worker_timeout_help)
    parser.add_argument("--formalize-worker-timeout", type=int, help=worker_timeout_help)
    parser.add_argument("--prioritize-open-problems-worker-timeout", type=int, help=worker_timeout_help)
    parser.add_argument("--skip-verify", action="store_true")
    parser.add_argument("--verify-timeout", type=int, default=600, help=verify_timeout_help)
    parser.add_argument("--paper-claim-retry-budget-sec", dest="paper_claim_retry_budget_sec", type=int, default=3600, help=retry_budget_help)
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
    if args.paper_claim_retry_budget_sec < 0:
        raise ValueError("--paper-claim-retry-budget-sec must be >= 0")
    if args.batch_generator_seed_count < 0:
        raise ValueError("--batch-generator-seed-count must be >= 0")
    if args.batch_generator_open_target_min < 0:
        raise ValueError("--batch-generator-open-target-min must be >= 0")

    verify_timeout_sec = None if args.verify_timeout == 0 else args.verify_timeout
    paper_claim_retry_budget_sec = (
        None if args.paper_claim_retry_budget_sec == 0 else args.paper_claim_retry_budget_sec
    )

    data_dir = Path(args.data_dir)
    scratch_file = Path(args.scratch_file)
    derived_file = Path(args.derived_file)
    theory_file = Path(args.theory_file)
    phase_attempts_path = Path(args.phase_attempts_file) if args.phase_attempts_file else None
    resume_session_events_path = (
        Path(args.resume_from_session_events_file)
        if args.resume_from_session_events_file
        else None
    )
    session_events_path = (
        Path(args.session_events_file)
        if args.session_events_file
        else (
            resume_session_events_path
            if resume_session_events_path is not None
            else data_dir / args.run_id / "paper_claim.events.jsonl"
        )
    )
    _initialize_jsonl_output(phase_attempts_path)
    if resume_session_events_path is None or session_events_path != resume_session_events_path:
        _initialize_jsonl_output(session_events_path)
    _, base_theory_context = load_theory_context(theory_file)
    derived_entries = extract_derived_theorem_entries(derived_file)

    worker_settings = None
    formalize_worker_settings = None
    prioritize_open_problems_worker_settings = None
    if args.enable_worker:
        _configure_problem_design_timeouts()
        if args.worker_timeout == 0:
            os.environ["ATC_WORKER_TIMEOUT"] = "0"
        if args.formalize_worker_timeout == 0:
            os.environ["ATC_FORMALIZE_WORKER_TIMEOUT"] = "0"
            os.environ["ATC_PAPER_CLAIM_CODEX_PROVE_WORKER_TIMEOUT"] = "0"
            os.environ["ATC_PAPER_CLAIM_CODEX_PROVE_CODEX_TIMEOUT"] = "0"
        worker_settings = load_worker_settings(
            command_override=args.worker_command,
            timeout_override=args.worker_timeout,
        )
        formalize_worker_settings = load_task_worker_settings(
            task_name="paper_claim_codex_prove",
            base_settings=worker_settings,
            timeout_override=args.formalize_worker_timeout,
            codex_timeout_override=args.formalize_worker_timeout,
        )
        prioritize_open_problems_worker_settings = load_task_worker_settings(
            task_name="prioritize_open_problems",
            base_settings=worker_settings,
            timeout_override=args.prioritize_open_problems_worker_timeout,
            codex_timeout_override=args.prioritize_open_problems_worker_timeout,
        )

    if resume_session_events_path is not None:
        report = resume_paper_claim_session_from_plan_event(
            resume_session_events_path=resume_session_events_path,
            resume_plan_id=args.resume_plan_id,
            worker_settings=worker_settings,
            scratch_file=scratch_file,
            derived_file=derived_file,
            derived_entries=derived_entries,
            data_dir=data_dir,
            base_theory_context=base_theory_context,
            formalize_worker_settings=formalize_worker_settings,
            paper_claim_planner_prompt_file="prompts/paper_claim/plan.md",
            paper_claim_codex_prove_prompt_file=".codex/workflow/paper_claim_codex_prove.md",
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
            failure_threshold=args.open_problem_failure_threshold,
            phase_logs=args.phase_logs,
            run_id=args.run_id,
            phase_attempts_path=phase_attempts_path,
            session_events_path=session_events_path,
            state_lock=threading.Lock(),
            derived_runtime_state={"generation": 0},
        )
    else:
        report = run_paper_claim_session(
            worker_settings=worker_settings,
            scratch_file=scratch_file,
            derived_file=derived_file,
            derived_entries=derived_entries,
            data_dir=data_dir,
            base_theory_context=base_theory_context,
            formalize_worker_settings=formalize_worker_settings,
            paper_claim_selector_prompt_file="prompts/paper_claim/select.md",
            paper_claim_retriever_prompt_file="prompts/paper_claim/retrieve.md",
            paper_claim_mapper_prompt_file="prompts/paper_claim/map.md",
            paper_claim_planner_prompt_file="prompts/paper_claim/plan.md",
            paper_claim_codex_prove_prompt_file=".codex/workflow/paper_claim_codex_prove.md",
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
            paper_claim_retry_budget_sec=paper_claim_retry_budget_sec,
            failure_threshold=args.open_problem_failure_threshold,
            phase_logs=args.phase_logs,
            run_id=args.run_id,
            phase_attempts_path=phase_attempts_path,
            session_events_path=session_events_path,
            state_lock=threading.Lock(),
            derived_runtime_state={"generation": 0},
        )
    report_json = json.dumps(report, ensure_ascii=False)
    if args.report_file:
        Path(args.report_file).write_text(report_json + "\n", encoding="utf-8")
    print(json.dumps(_build_stdout_summary(report, report_file=args.report_file), ensure_ascii=False))


if __name__ == "__main__":
    main()
