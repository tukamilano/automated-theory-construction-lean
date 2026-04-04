from __future__ import annotations

import argparse
import time
from pathlib import Path

from apply_derived_compression_plan import run_apply_derived_compression_plan
from common import write_json_atomic
from derived_refactor_utils import build_report
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


def _remaining_wall_clock_sec(deadline: float | None) -> int | None:
    if deadline is None:
        return None
    remaining = int(deadline - time.monotonic())
    return max(0, remaining)


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
    deadline = None if args.max_wall_clock_sec in (None, 0) else time.monotonic() + args.max_wall_clock_sec

    try:
        planner_reports: list[dict[str, object]] = []
        executor_reports: list[dict[str, object]] = []
        working_input = input_file
        accepted_cycles = 0
        last_plan_report: dict[str, object] | None = None
        last_executor_report: dict[str, object] | None = None
        final_status = "noop"
        final_stop_reason = "no_candidates"
        final_stop_detail = "planner returned no items"

        while True:
            remaining_sec = _remaining_wall_clock_sec(deadline)
            if deadline is not None and remaining_sec == 0:
                final_status = "stopped" if accepted_cycles > 0 else "noop"
                final_stop_reason = "budget_exhausted"
                final_stop_detail = "max_wall_clock_reached before planning a new item"
                break

            plan_report = run_plan_derived_compression(
                input_file=working_input,
                theory_file=theory_file,
                prompt_file=planner_prompt_file,
                theorem_reuse_memory_file=theorem_reuse_memory_file,
                output_file=plan_file,
                worker_command=args.worker_command,
                worker_timeout=args.worker_timeout,
            )
            planner_reports.append(plan_report)
            last_plan_report = plan_report

            if plan_report.get("status") == "error":
                final_report = build_report(
                    "error",
                    str(plan_report.get("stop_reason", "worker_error")),
                    stop_detail=str(plan_report.get("stop_detail", "")),
                    input_file=input_file,
                    output_file=output_file,
                    report_file=report_file,
                    extra={
                        "planner_reports": planner_reports,
                        "executor_reports": executor_reports,
                        "planner": last_plan_report,
                        "executor": last_executor_report,
                        "accepted_cycles": accepted_cycles,
                        "plan_file": str(plan_file),
                        "progress_log_file": str(progress_log_file) if progress_log_file is not None else None,
                    },
                )
                write_report(report_file, final_report)
                print_report(final_report)
                raise SystemExit(1)

            if int(plan_report.get("item_count", 0) or 0) == 0:
                final_status = "ok" if accepted_cycles > 0 else "noop"
                final_stop_reason = "no_candidates"
                final_stop_detail = "planner returned no items"
                break

            plan_payload = {
                "plan_version": 1,
                "source_file": str(working_input),
                "summary": str(plan_report.get("summary", "")),
                "items": [],
            }
            try:
                import json

                loaded_plan = json.loads(plan_file.read_text(encoding="utf-8"))
                if isinstance(loaded_plan, dict):
                    plan_payload["plan_version"] = int(loaded_plan.get("plan_version", 1) or 1)
                    plan_payload["source_file"] = str(loaded_plan.get("source_file", working_input))
                    plan_payload["summary"] = str(loaded_plan.get("summary", "")).strip()
                    items = loaded_plan.get("items", [])
                    if isinstance(items, list) and items:
                        plan_payload["items"] = [items[0]]
            except Exception:
                plan_payload["items"] = []

            if not plan_payload["items"]:
                final_status = "ok" if accepted_cycles > 0 else "noop"
                final_stop_reason = "no_candidates"
                final_stop_detail = "planner returned no usable items"
                break

            write_json_atomic(plan_file, plan_payload)

            remaining_sec = _remaining_wall_clock_sec(deadline)
            if deadline is not None and remaining_sec == 0:
                final_status = "stopped" if accepted_cycles > 0 else "noop"
                final_stop_reason = "budget_exhausted"
                final_stop_detail = "max_wall_clock_reached before executing the planned item"
                break

            executor_report = run_apply_derived_compression_plan(
                input_file=working_input,
                plan_file=plan_file,
                output_file=output_file,
                report_file=report_file,
                prompt_file=executor_prompt_file,
                theorem_reuse_memory_file=theorem_reuse_memory_file,
                progress_log_file=progress_log_file,
                verify_timeout_sec=args.verify_timeout,
                max_wall_clock_sec=remaining_sec,
                worker_command=args.worker_command,
                worker_timeout=args.worker_timeout,
            )
            executor_reports.append(executor_report)
            last_executor_report = executor_report

            accepted_count = int(executor_report.get("accepted_count", 0) or 0)
            if str(executor_report.get("status", "")) == "error":
                final_status = "error"
                final_stop_reason = str(executor_report.get("stop_reason", "worker_error"))
                final_stop_detail = str(executor_report.get("stop_detail", ""))
                break
            if accepted_count != 1:
                final_status = str(executor_report.get("status", "ok"))
                final_stop_reason = str(executor_report.get("stop_reason", "completed"))
                final_stop_detail = str(executor_report.get("stop_detail", ""))
                break

            accepted_cycles += 1
            working_input = output_file
            final_status = "ok"
            final_stop_reason = "completed"
            final_stop_detail = ""

        final_report = build_report(
            final_status,
            final_stop_reason,
            stop_detail=final_stop_detail,
            input_file=input_file,
            output_file=output_file,
            report_file=report_file,
            extra={
                "planner_reports": planner_reports,
                "executor_reports": executor_reports,
                "planner": last_plan_report,
                "executor": last_executor_report,
                "accepted_cycles": accepted_cycles,
                "plan_file": str(plan_file),
                "progress_log_file": str(progress_log_file) if progress_log_file is not None else None,
            },
        )
        write_report(report_file, final_report)
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
        print_report(final_report)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
