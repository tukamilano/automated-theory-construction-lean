from __future__ import annotations

import argparse
from pathlib import Path

from apply_derived_compression_plan import run_apply_derived_compression_plan
from derived_refactor_utils import build_report
from derived_refactor_utils import emit_progress_finish
from derived_refactor_utils import emit_progress_start
from derived_refactor_utils import print_report
from derived_refactor_utils import write_report
from plan_derived_compression import run_plan_derived_compression


DEFAULT_INPUT = Path("AutomatedTheoryConstruction/Derived.refactored.preview.lean")
DEFAULT_THEORY = Path("AutomatedTheoryConstruction/Theory.lean")
DEFAULT_PLAN = Path("AutomatedTheoryConstruction/Derived.compression.plan.json")
DEFAULT_REPORT = Path("AutomatedTheoryConstruction/Derived.compression.report.json")
DEFAULT_PROGRESS_LOG = Path("AutomatedTheoryConstruction/Derived.compression.executor.log.jsonl")
DEFAULT_PLANNER_PROMPT = Path("prompts/derived_compression_planner.md")
DEFAULT_EXECUTOR_PROMPT = Path("prompts/derived_compression_executor.md")
DEFAULT_THEOREM_REUSE_MEMORY = Path("data/theorem_reuse_memory.json")


def main() -> None:
    parser = argparse.ArgumentParser(description="Run pass 1.2 soft compression for Derived preview files.")
    parser.add_argument("--input-file", default=str(DEFAULT_INPUT))
    parser.add_argument("--output-file", default=str(DEFAULT_INPUT))
    parser.add_argument("--theory-file", default=str(DEFAULT_THEORY))
    parser.add_argument("--plan-file", default=str(DEFAULT_PLAN))
    parser.add_argument("--report-file", default=str(DEFAULT_REPORT))
    parser.add_argument("--progress-log-file", default=str(DEFAULT_PROGRESS_LOG))
    parser.add_argument("--planner-prompt-file", default=str(DEFAULT_PLANNER_PROMPT))
    parser.add_argument("--executor-prompt-file", default=str(DEFAULT_EXECUTOR_PROMPT))
    parser.add_argument("--theorem-reuse-memory-file", default=str(DEFAULT_THEOREM_REUSE_MEMORY))
    parser.add_argument("--worker-command")
    parser.add_argument("--worker-timeout", type=int, help="Per worker subprocess timeout in seconds.")
    parser.add_argument("--verify-timeout", type=int, help="Per Lean verification timeout in seconds.")
    parser.add_argument("--max-wall-clock-sec", type=int, help="Total retry budget for pass 1.2 in seconds.")
    args = parser.parse_args()
    input_file = Path(args.input_file)
    output_file = Path(args.output_file)
    theory_file = Path(args.theory_file)
    plan_file = Path(args.plan_file)
    report_file = Path(args.report_file)
    progress_log_file = Path(args.progress_log_file) if args.progress_log_file else None
    planner_prompt_file = Path(args.planner_prompt_file)
    executor_prompt_file = Path(args.executor_prompt_file)
    theorem_reuse_memory_file = Path(args.theorem_reuse_memory_file)

    try:
        plan_report = run_plan_derived_compression(
            input_file=input_file,
            theory_file=theory_file,
            prompt_file=planner_prompt_file,
            theorem_reuse_memory_file=theorem_reuse_memory_file,
            output_file=plan_file,
            worker_command=args.worker_command,
            worker_timeout=args.worker_timeout,
        )

        if plan_report.get("status") == "error":
            final_report = build_report(
                "error",
                str(plan_report.get("stop_reason", "worker_error")),
                stop_detail=str(plan_report.get("stop_detail", "")),
                input_file=input_file,
                output_file=output_file,
                report_file=report_file,
                extra={
                    "planner": plan_report,
                    "executor": None,
                    "plan_file": str(plan_file),
                    "progress_log_file": str(progress_log_file) if progress_log_file is not None else None,
                },
            )
            write_report(report_file, final_report)
            emit_progress_finish(
                progress_log_file,
                pass_name="pass_1.2",
                round=0,
                result="error",
                stop_reason=str(plan_report.get("stop_reason", "worker_error")),
                error_excerpt=str(plan_report.get("stop_detail", "")),
            )
            print_report(final_report)
            raise SystemExit(1)

        if int(plan_report.get("item_count", 0) or 0) == 0:
            emit_progress_start(progress_log_file, pass_name="pass_1.2")
            emit_progress_finish(
                progress_log_file,
                pass_name="pass_1.2",
                round=0,
                result="noop",
                stop_reason="no_candidates",
            )
            final_report = build_report(
                "noop",
                "no_candidates",
                stop_detail="planner returned no items",
                input_file=input_file,
                output_file=output_file,
                report_file=report_file,
                extra={
                    "planner": plan_report,
                    "executor": None,
                    "plan_file": str(plan_file),
                    "progress_log_file": str(progress_log_file) if progress_log_file is not None else None,
                },
            )
            write_report(report_file, final_report)
            print_report(final_report)
            return

        executor_report = run_apply_derived_compression_plan(
            input_file=input_file,
            plan_file=plan_file,
            output_file=output_file,
            report_file=report_file,
            prompt_file=executor_prompt_file,
            theorem_reuse_memory_file=theorem_reuse_memory_file,
            progress_log_file=progress_log_file,
            verify_timeout_sec=args.verify_timeout,
            max_wall_clock_sec=args.max_wall_clock_sec,
            worker_command=args.worker_command,
            worker_timeout=args.worker_timeout,
        )
        final_report = build_report(
            str(executor_report.get("status", "ok")),
            str(executor_report.get("stop_reason", "completed")),
            stop_detail=str(executor_report.get("stop_detail", "")),
            input_file=input_file,
            output_file=output_file,
            report_file=report_file,
            extra={
                "planner": plan_report,
                "executor": executor_report,
                "plan_file": str(plan_file),
                "progress_log_file": str(progress_log_file) if progress_log_file is not None else None,
            },
        )
        print_report(final_report)
    except Exception as exc:
        final_report = build_report(
            "error",
            "worker_error",
            stop_detail=str(exc),
            input_file=input_file,
            output_file=output_file,
            report_file=report_file,
            extra={
                "planner": None,
                "executor": None,
                "plan_file": str(plan_file),
                "progress_log_file": str(progress_log_file) if progress_log_file is not None else None,
            },
        )
        write_report(report_file, final_report)
        emit_progress_finish(
            progress_log_file,
            pass_name="pass_1.2",
            round=0,
            result="error",
            stop_reason="worker_error",
        )
        print_report(final_report)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
