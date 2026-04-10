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
from refactor_pass_specs import RefactorPassSpec


def _remaining_wall_clock_sec(deadline: float | None) -> int | None:
    if deadline is None:
        return None
    remaining = int(deadline - time.monotonic())
    return max(0, remaining)


def run_refactor_pass(
    spec: RefactorPassSpec,
    *,
    input_file: Path,
    output_file: Path,
    theory_file: Path,
    plan_file: Path,
    report_file: Path | None,
    progress_log_file: Path | None,
    planner_prompt_file: Path,
    executor_prompt_file: Path,
    theorem_reuse_memory_file: Path,
    worker_command: str | None = None,
    worker_timeout: int | None = None,
    verify_timeout: int | None = None,
    max_wall_clock_sec: int | None = None,
    print_final_report: bool = False,
) -> dict[str, object]:
    deadline = None if max_wall_clock_sec in (None, 0) else time.monotonic() + max_wall_clock_sec
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
                worker_command=worker_command,
                worker_timeout=worker_timeout,
                allowed_kinds=set(spec.allowed_kinds),
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
                if print_final_report:
                    print_report(final_report)
                return final_report

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
                        cleaned_items = [item for item in items if isinstance(item, dict)]
                        if cleaned_items:
                            plan_payload["items"] = [cleaned_items[0]]
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
                verify_timeout_sec=verify_timeout,
                max_wall_clock_sec=remaining_sec,
                pass_name=spec.pass_name,
                allow_repair=spec.allow_repair,
                worker_command=worker_command,
                worker_timeout=worker_timeout,
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
        if print_final_report:
            print_report(final_report)
        return final_report
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
        if print_final_report:
            print_report(final_report)
        return final_report


def run_refactor_pass_cli(spec: RefactorPassSpec) -> None:
    parser = argparse.ArgumentParser(description=spec.cli_description)
    parser.add_argument("--input-file", default=str(spec.default_input))
    parser.add_argument("--output-file", default=str(spec.default_input))
    parser.add_argument("--theory-file", default=str(spec.default_theory))
    parser.add_argument("--plan-file", default=str(spec.default_plan))
    parser.add_argument("--report-file", default=str(spec.default_report))
    parser.add_argument("--progress-log-file", default=str(spec.default_progress_log))
    parser.add_argument("--planner-prompt-file", default=str(spec.default_planner_prompt))
    parser.add_argument("--executor-prompt-file", default=str(spec.default_executor_prompt))
    parser.add_argument("--theorem-reuse-memory-file", default=str(spec.default_theorem_reuse_memory))
    parser.add_argument("--worker-command")
    parser.add_argument("--worker-timeout", type=int, help="Per worker subprocess timeout in seconds.")
    parser.add_argument("--verify-timeout", type=int, help="Per Lean verification timeout in seconds.")
    parser.add_argument("--max-wall-clock-sec", type=int, help=f"Total retry budget for {spec.pass_name} in seconds.")
    args = parser.parse_args()

    report = run_refactor_pass(
        spec,
        input_file=Path(args.input_file),
        output_file=Path(args.output_file),
        theory_file=Path(args.theory_file),
        plan_file=Path(args.plan_file),
        report_file=Path(args.report_file),
        progress_log_file=Path(args.progress_log_file) if args.progress_log_file else None,
        planner_prompt_file=Path(args.planner_prompt_file),
        executor_prompt_file=Path(args.executor_prompt_file),
        theorem_reuse_memory_file=Path(args.theorem_reuse_memory_file),
        worker_command=args.worker_command,
        worker_timeout=args.worker_timeout,
        verify_timeout=args.verify_timeout,
        max_wall_clock_sec=args.max_wall_clock_sec,
        print_final_report=True,
    )
    if str(report.get("status", "")) == "error":
        raise SystemExit(1)
