from __future__ import annotations

import argparse
import shlex
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_THEORY = Path("AutomatedTheoryConstruction/Theory.lean")
DEFAULT_DERIVED = Path("AutomatedTheoryConstruction/Derived.lean")
DEFAULT_SEEDS = Path("AutomatedTheoryConstruction/seeds.jsonl")
DEFAULT_PREVIEW = Path("AutomatedTheoryConstruction/Derived.refactored.preview.lean")
DEFAULT_COMPRESSION_PLAN = Path("AutomatedTheoryConstruction/Derived.compression.plan.json")
DEFAULT_COMPRESSION_REPORT = Path("AutomatedTheoryConstruction/Derived.compression.report.json")
DEFAULT_REFACTOR_PROGRESS_LOG = Path("AutomatedTheoryConstruction/Derived.refactor.pass1.log.jsonl")
DEFAULT_COMPRESSION_PROGRESS_LOG = Path("AutomatedTheoryConstruction/Derived.compression.executor.log.jsonl")
DEFAULT_PROOF_RETARGET_PLAN = Path("AutomatedTheoryConstruction/Derived.proof_retarget.plan.json")
DEFAULT_PROOF_RETARGET_REPORT = Path("AutomatedTheoryConstruction/Derived.proof_retarget.report.json")
DEFAULT_PROOF_RETARGET_PROGRESS_LOG = Path("AutomatedTheoryConstruction/Derived.proof_retarget.executor.log.jsonl")
DEFAULT_PRESENTATION_PLAN = Path("AutomatedTheoryConstruction/Derived.presentation.plan.json")
DEFAULT_PRESENTATION_REPORT = Path("AutomatedTheoryConstruction/Derived.presentation.report.json")
DEFAULT_PRESENTATION_PROGRESS_LOG = Path("AutomatedTheoryConstruction/Derived.presentation.executor.log.jsonl")
DEFAULT_REVIEWED = Path("AutomatedTheoryConstruction/Derived.refactored.reviewed.lean")
DEFAULT_REVIEW_REPORT = Path("AutomatedTheoryConstruction/Derived.refactored.reviewed.report.json")
DEFAULT_TRY_AT_EACH_STEP_RAW = Path("AutomatedTheoryConstruction/Derived.tryAtEachStep.json")
DEFAULT_TRY_AT_EACH_STEP_REPORT = Path("AutomatedTheoryConstruction/Derived.tryAtEachStep.apply_report.json")
LEAN_BUILD_TARGETS = (
    "AutomatedTheoryConstruction.Theory",
    "AutomatedTheoryConstruction.Derived",
)


def append_optional_flag(cmd: list[str], flag: str, value: str | int | None) -> None:
    if value is None:
        return
    text = str(value).strip()
    if not text:
        return
    cmd.extend([flag, text])


def cleanup_pipeline_artifacts(paths: list[str]) -> None:
    seen: set[Path] = set()
    for raw_path in paths:
        path = Path(raw_path)
        if path in seen:
            continue
        seen.add(path)
        path.unlink(missing_ok=True)


def run_stage(
    name: str,
    cmd: list[str],
    *,
    dry_run: bool,
    capture_output: bool = False,
) -> subprocess.CompletedProcess[str] | None:
    print(f"[pipeline] {name}: {shlex.join(cmd)}", file=sys.stderr, flush=True)
    if dry_run:
        return None

    completed = subprocess.run(
        cmd,
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=capture_output,
        text=capture_output,
    )
    if capture_output:
        if completed.stdout:
            sys.stdout.write(completed.stdout)
            sys.stdout.flush()
        if completed.stderr:
            sys.stderr.write(completed.stderr)
            sys.stderr.flush()
    return completed


def require_success(stage_name: str, completed: subprocess.CompletedProcess[str] | None) -> None:
    if completed is not None and completed.returncode != 0:
        print(
            f"[pipeline] {stage_name} failed with exit code {completed.returncode}",
            file=sys.stderr,
            flush=True,
        )
        raise SystemExit(completed.returncode)


def stage_timed_out(completed: subprocess.CompletedProcess[str] | None) -> bool:
    if completed is None or completed.returncode == 0:
        return False
    combined = "\n".join(part for part in (completed.stdout, completed.stderr) if part).lower()
    return "timed out after" in combined or "timeoutexpired" in combined


def build_seed_command(args: argparse.Namespace) -> list[str]:
    cmd = [
        "uv",
        "run",
        "python",
        "scripts/generate_seeds_from_theory.py",
        "--theory-file",
        str(DEFAULT_THEORY),
        "--derived-file",
        str(DEFAULT_DERIVED),
        "--output-file",
        str(DEFAULT_SEEDS),
        "--seed-count",
        str(args.seed_count),
        "--seed-src",
        args.seed_src,
        "--sandbox",
        args.seed_sandbox,
    ]
    append_optional_flag(cmd, "--extra-instruction", args.seed_extra_instruction)
    append_optional_flag(cmd, "--model", args.seed_model)
    if not args.initialize_on_start:
        cmd.append("--no-initialize-runtime-state")
    for path in args.context_files:
        cmd.extend(["--context-file", path])
    return cmd


def build_loop_command(args: argparse.Namespace) -> list[str]:
    cmd = [
        "uv",
        "run",
        "python",
        "scripts/run_loop.py",
        "--no-initialize-on-start",
    ]
    if not args.phase_logs:
        cmd.append("--no-phase-logs")
    if args.skip_loop_verify:
        cmd.append("--skip-verify")

    append_optional_flag(cmd, "--max-iterations", args.max_iterations)
    append_optional_flag(cmd, "--parallel-sessions", args.parallel_sessions)
    append_optional_flag(cmd, "--worker-command", args.worker_command)
    append_optional_flag(cmd, "--worker-timeout", args.worker_timeout)
    append_optional_flag(cmd, "--prover-worker-command", args.prover_worker_command)
    append_optional_flag(cmd, "--prover-worker-timeout", args.prover_worker_timeout)
    append_optional_flag(cmd, "--prover-statement-worker-command", args.prover_statement_worker_command)
    append_optional_flag(cmd, "--prover-statement-worker-timeout", args.prover_statement_worker_timeout)
    append_optional_flag(cmd, "--formalize-worker-command", args.formalize_worker_command)
    append_optional_flag(cmd, "--formalize-worker-timeout", args.formalize_worker_timeout)
    append_optional_flag(cmd, "--repair-worker-command", args.repair_worker_command)
    append_optional_flag(cmd, "--repair-worker-timeout", args.repair_worker_timeout)
    append_optional_flag(cmd, "--prioritize-open-problems-worker-command", args.prioritize_open_problems_worker_command)
    append_optional_flag(cmd, "--prioritize-open-problems-worker-timeout", args.prioritize_open_problems_worker_timeout)
    append_optional_flag(cmd, "--open-problem-failure-threshold", args.open_problem_failure_threshold)
    append_optional_flag(cmd, "--prover-retry-budget-sec", args.prover_retry_budget_sec)
    append_optional_flag(cmd, "--formalization-retry-budget-sec", args.formalization_retry_budget_sec)
    append_optional_flag(cmd, "--max-same-error-streak", args.max_same_error_streak)
    if args.run_main_theorem_session:
        append_optional_flag(cmd, "--main-theorem-interval", args.main_theorem_interval)
    else:
        cmd.extend(["--main-theorem-interval", "0"])
    append_optional_flag(
        cmd,
        "--main-theorem-formalize-worker-timeout",
        args.main_theorem_formalize_worker_timeout,
    )
    append_optional_flag(
        cmd,
        "--main-theorem-repair-worker-timeout",
        args.main_theorem_repair_worker_timeout,
    )
    append_optional_flag(cmd, "--main-theorem-verify-timeout", args.main_theorem_verify_timeout)
    append_optional_flag(
        cmd,
        "--main-theorem-formalization-retry-budget-sec",
        args.main_theorem_formalization_retry_budget_sec,
    )
    return cmd


def build_refactor_command(args: argparse.Namespace) -> list[str]:
    cmd = [
        "uv",
        "run",
        "python",
        "scripts/refactor_derived.py",
        "--derived-file",
        str(DEFAULT_DERIVED),
        "--theory-file",
        str(DEFAULT_THEORY),
        "--output-file",
        args.preview_file,
    ]
    refactor_worker_command = args.refactor_worker_command or args.worker_command
    refactor_worker_timeout = args.refactor_worker_timeout
    append_optional_flag(cmd, "--worker-command", refactor_worker_command)
    append_optional_flag(cmd, "--worker-timeout", refactor_worker_timeout)
    append_optional_flag(cmd, "--verify-timeout", args.refactor_verify_timeout)
    append_optional_flag(cmd, "--progress-log-file", args.refactor_progress_log_file)
    append_optional_flag(cmd, "--max-wall-clock-sec", args.refactor_max_wall_clock_sec)
    return cmd


def build_compress_command(args: argparse.Namespace) -> list[str]:
    cmd = [
        "uv",
        "run",
        "python",
        "scripts/run_compression_pass.py",
        "--input-file",
        args.preview_file,
        "--output-file",
        args.preview_file,
        "--theory-file",
        str(DEFAULT_THEORY),
        "--plan-file",
        args.compression_plan_file,
        "--report-file",
        args.compression_report_file,
        "--progress-log-file",
        args.compression_progress_log_file,
    ]
    refactor_worker_command = args.refactor_worker_command or args.worker_command
    refactor_worker_timeout = args.refactor_worker_timeout
    append_optional_flag(cmd, "--worker-command", refactor_worker_command)
    append_optional_flag(cmd, "--worker-timeout", refactor_worker_timeout)
    append_optional_flag(cmd, "--verify-timeout", args.refactor_verify_timeout)
    append_optional_flag(cmd, "--max-wall-clock-sec", args.compression_max_wall_clock_sec)
    return cmd


def build_proof_retarget_command(args: argparse.Namespace) -> list[str]:
    cmd = [
        "uv",
        "run",
        "python",
        "scripts/run_proof_retarget_pass.py",
        "--input-file",
        args.preview_file,
        "--output-file",
        args.preview_file,
        "--theory-file",
        str(DEFAULT_THEORY),
        "--plan-file",
        args.proof_retarget_plan_file,
        "--report-file",
        args.proof_retarget_report_file,
        "--progress-log-file",
        args.proof_retarget_progress_log_file,
    ]
    refactor_worker_command = args.refactor_worker_command or args.worker_command
    refactor_worker_timeout = args.refactor_worker_timeout
    append_optional_flag(cmd, "--worker-command", refactor_worker_command)
    append_optional_flag(cmd, "--worker-timeout", refactor_worker_timeout)
    append_optional_flag(cmd, "--verify-timeout", args.refactor_verify_timeout)
    append_optional_flag(cmd, "--max-wall-clock-sec", args.proof_retarget_max_wall_clock_sec)
    return cmd


def build_presentation_command(args: argparse.Namespace) -> list[str]:
    cmd = [
        "uv",
        "run",
        "python",
        "scripts/run_presentation_pass.py",
        "--input-file",
        args.preview_file,
        "--output-file",
        args.preview_file,
        "--theory-file",
        str(DEFAULT_THEORY),
        "--plan-file",
        args.presentation_plan_file,
        "--report-file",
        args.presentation_report_file,
        "--progress-log-file",
        args.presentation_progress_log_file,
    ]
    refactor_worker_command = args.refactor_worker_command or args.worker_command
    refactor_worker_timeout = args.refactor_worker_timeout
    append_optional_flag(cmd, "--worker-command", refactor_worker_command)
    append_optional_flag(cmd, "--worker-timeout", refactor_worker_timeout)
    append_optional_flag(cmd, "--verify-timeout", args.refactor_verify_timeout)
    append_optional_flag(cmd, "--max-wall-clock-sec", args.presentation_max_wall_clock_sec)
    return cmd


def build_review_command_with_input(args: argparse.Namespace, *, input_file: str) -> list[str]:
    cmd = [
        "uv",
        "run",
        "python",
        "scripts/direct_refactor_derived.py",
        "--input-file",
        input_file,
        "--output-file",
        args.review_output_file,
        "--report-file",
        args.review_report_file,
        "--sandbox",
        args.review_sandbox,
    ]
    append_optional_flag(cmd, "--model", args.review_model)
    if args.no_review_verify:
        cmd.append("--no-verify")
    return cmd


def build_rewrite_command(args: argparse.Namespace, *, input_file: str, output_file: str) -> list[str]:
    cmd = [
        "uv",
        "run",
        "python",
        "scripts/apply_try_at_each_step_rewrites.py",
        "--input-file",
        input_file,
        "--output-file",
        output_file,
        "--raw-output-file",
        args.try_at_each_step_raw_output_file,
        "--apply-report-file",
        args.try_at_each_step_apply_report_file,
        "--tactic",
        args.try_at_each_step_tactic,
    ]
    append_optional_flag(cmd, "--verify-timeout", args.try_at_each_step_verify_timeout)
    return cmd


def _add_context_flags(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--article-file",
        "--context-file",
        dest="context_files",
        action="append",
        default=[],
        help="Extra article/context file to read during seed generation. Repeatable.",
    )


def _add_loop_flags(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--max-iterations", type=int)
    parser.add_argument("--parallel-sessions", type=int, default=1)
    parser.add_argument("--skip-loop-verify", action="store_true")


def _add_initialize_phase_flags(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--initialize-on-start", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--phase-logs", action=argparse.BooleanOptionalAction, default=True)


def _add_main_worker_flags(parser: argparse.ArgumentParser, *, worker_timeout_help: str) -> None:
    parser.add_argument("--worker-command")
    parser.add_argument("--worker-timeout", type=int, help=worker_timeout_help)
    task_prefixes = ("prover", "prover-statement", "formalize", "repair", "prioritize-open-problems")
    for prefix in task_prefixes:
        parser.add_argument(f"--{prefix}-worker-command")
        parser.add_argument(f"--{prefix}-worker-timeout", type=int, help=worker_timeout_help)
    parser.add_argument("--refactor-worker-command")
    parser.add_argument("--refactor-worker-timeout", type=int, help=worker_timeout_help)


def _add_budget_flags(parser: argparse.ArgumentParser) -> None:
    retry_budget_help = "Whole retry-loop budget in seconds."
    parser.add_argument("--refactor-max-wall-clock-sec", type=int, help="Whole pass 1 wall-clock budget in seconds.")
    parser.add_argument("--compression-max-wall-clock-sec", type=int, help="Whole pass 1.2 wall-clock budget in seconds.")
    parser.add_argument("--proof-retarget-max-wall-clock-sec", type=int, help="Whole pass 1.3 wall-clock budget in seconds.")
    parser.add_argument("--presentation-max-wall-clock-sec", type=int, help="Whole pass 1.4 wall-clock budget in seconds.")
    parser.add_argument("--prover-retry-budget-sec", type=int, help=retry_budget_help)
    parser.add_argument("--formalization-retry-budget-sec", type=int, help=retry_budget_help)
    parser.add_argument("--main-theorem-formalization-retry-budget-sec", type=int, help=retry_budget_help)


def _add_loop_tuning_flags(parser: argparse.ArgumentParser, *, worker_timeout_help: str, verify_timeout_help: str) -> None:
    parser.add_argument("--open-problem-failure-threshold", type=int)
    parser.add_argument("--main-theorem-interval", type=int)
    parser.add_argument("--main-theorem-formalize-worker-timeout", type=int, help=worker_timeout_help)
    parser.add_argument("--main-theorem-repair-worker-timeout", type=int, help=worker_timeout_help)
    parser.add_argument("--main-theorem-verify-timeout", type=int, help=verify_timeout_help)
    parser.add_argument("--max-same-error-streak", type=int)


def _add_pass_toggles(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--run-seed", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--run-refactor-pass-1", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--run-refactor-pass-1_2", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--run-refactor-pass-1_3", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--run-refactor-pass-1_4", action=argparse.BooleanOptionalAction, default=False)
    parser.add_argument("--run-refactor-pass-1_5", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--run-refactor-pass-2", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--run-main-theorem-session", action=argparse.BooleanOptionalAction, default=True)


def _add_path_flags(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--preview-file", default=str(DEFAULT_PREVIEW))
    parser.add_argument("--compression-plan-file", default=str(DEFAULT_COMPRESSION_PLAN))
    parser.add_argument("--compression-report-file", default=str(DEFAULT_COMPRESSION_REPORT))
    parser.add_argument("--proof-retarget-plan-file", default=str(DEFAULT_PROOF_RETARGET_PLAN))
    parser.add_argument("--proof-retarget-report-file", default=str(DEFAULT_PROOF_RETARGET_REPORT))
    parser.add_argument("--presentation-plan-file", default=str(DEFAULT_PRESENTATION_PLAN))
    parser.add_argument("--presentation-report-file", default=str(DEFAULT_PRESENTATION_REPORT))
    parser.add_argument("--refactor-progress-log-file", default=str(DEFAULT_REFACTOR_PROGRESS_LOG))
    parser.add_argument("--compression-progress-log-file", default=str(DEFAULT_COMPRESSION_PROGRESS_LOG))
    parser.add_argument("--proof-retarget-progress-log-file", default=str(DEFAULT_PROOF_RETARGET_PROGRESS_LOG))
    parser.add_argument("--presentation-progress-log-file", default=str(DEFAULT_PRESENTATION_PROGRESS_LOG))
    parser.add_argument("--review-output-file", default=str(DEFAULT_REVIEWED))
    parser.add_argument("--review-report-file", default=str(DEFAULT_REVIEW_REPORT))
    parser.add_argument("--try-at-each-step-raw-output-file", default=str(DEFAULT_TRY_AT_EACH_STEP_RAW))
    parser.add_argument("--try-at-each-step-apply-report-file", default=str(DEFAULT_TRY_AT_EACH_STEP_REPORT))


def _add_rewrite_and_review_flags(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--try-at-each-step-tactic", default="with_reducible exact?")
    parser.add_argument("--try-at-each-step-verify-timeout", type=int, help="Per Lean verification timeout in seconds.")
    parser.add_argument("--review-model")
    parser.add_argument("--review-sandbox", default="workspace-write")
    parser.add_argument("--no-review-verify", action="store_true")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate seeds from the active Theory.lean entry module, its local imports, and context files, run the loop, "
            "then run the Derived refactor / pass 1.2 / pass 1.3 / optional pass 1.4 / rewrite / review passes."
        )
    )
    worker_timeout_help = "Per worker subprocess timeout in seconds."
    verify_timeout_help = "Per Lean verification timeout in seconds."
    _add_context_flags(parser)
    parser.add_argument("--seed-count", type=int, default=4)
    parser.add_argument("--seed-src", default="seed")
    parser.add_argument("--seed-extra-instruction", default="")
    parser.add_argument("--seed-model")
    parser.add_argument("--seed-sandbox", default="read-only")
    _add_initialize_phase_flags(parser)
    _add_loop_flags(parser)
    _add_main_worker_flags(parser, worker_timeout_help=worker_timeout_help)
    parser.add_argument("--refactor-verify-timeout", type=int, help=verify_timeout_help)
    _add_loop_tuning_flags(
        parser,
        worker_timeout_help=worker_timeout_help,
        verify_timeout_help=verify_timeout_help,
    )
    _add_budget_flags(parser)
    _add_path_flags(parser)
    _add_rewrite_and_review_flags(parser)
    _add_pass_toggles(parser)
    parser.add_argument("--dry-run", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()

    if args.initialize_on_start and not args.dry_run:
        cleanup_pipeline_artifacts(
            [
                args.preview_file,
                args.compression_plan_file,
                args.compression_report_file,
                args.proof_retarget_plan_file,
                args.proof_retarget_report_file,
                args.presentation_plan_file,
                args.presentation_report_file,
                args.refactor_progress_log_file,
                args.compression_progress_log_file,
                args.proof_retarget_progress_log_file,
                args.presentation_progress_log_file,
                args.review_output_file,
                args.review_report_file,
                args.try_at_each_step_raw_output_file,
                args.try_at_each_step_apply_report_file,
            ]
        )

    seed_cmd = build_seed_command(args)
    loop_cmd = build_loop_command(args)
    refactor_cmd = build_refactor_command(args)
    compress_cmd = build_compress_command(args)
    proof_retarget_cmd = build_proof_retarget_command(args)
    presentation_cmd = build_presentation_command(args)
    rewrite_input = args.preview_file
    rewrite_output = args.preview_file
    review_input = args.preview_file
    can_run_pass_1_2 = True
    can_run_pass_1_3 = True
    can_run_pass_1_4 = True

    if args.run_seed:
        require_success("seed-generation", run_stage("seed-generation", seed_cmd, dry_run=args.dry_run))
    else:
        print("[pipeline] seed-generation: skipped (--no-run-seed)", file=sys.stderr, flush=True)

    # Seed initialization is the only stage that already runs the stable Lean prebuild.
    if not (args.run_seed and args.initialize_on_start):
        for target in LEAN_BUILD_TARGETS:
            stage_name = f"lean-prebuild:{target}"
            require_success(
                stage_name,
                run_stage(stage_name, ["lake", "build", target], dry_run=args.dry_run, capture_output=True),
            )

    require_success("main-loop", run_stage("main-loop", loop_cmd, dry_run=args.dry_run))

    if args.run_refactor_pass_1:
        refactor_result = run_stage("refactor-pass-1", refactor_cmd, dry_run=args.dry_run, capture_output=True)
        if stage_timed_out(refactor_result):
            print(
                "[pipeline] refactor-pass-1 timed out; falling back to direct review from Derived.lean",
                file=sys.stderr,
                flush=True,
            )
            rewrite_input = str(DEFAULT_DERIVED)
            rewrite_output = args.preview_file
            review_input = str(DEFAULT_DERIVED)
            can_run_pass_1_2 = False
            can_run_pass_1_3 = False
            can_run_pass_1_4 = False
        else:
            require_success("refactor-pass-1", refactor_result)
    else:
        print("[pipeline] refactor-pass-1: skipped (--no-run-refactor-pass-1)", file=sys.stderr, flush=True)
        rewrite_input = str(DEFAULT_DERIVED)
        rewrite_output = args.preview_file
        review_input = str(DEFAULT_DERIVED)
        can_run_pass_1_2 = False
        can_run_pass_1_3 = False
        can_run_pass_1_4 = False

    if args.run_refactor_pass_1_2 and can_run_pass_1_2:
        compress_result = run_stage("refactor-pass-1_2", compress_cmd, dry_run=args.dry_run, capture_output=True)
        if compress_result is None or compress_result.returncode == 0:
            review_input = args.preview_file
        else:
            print(
                "[pipeline] refactor-pass-1_2 failed; keeping preview input from pass 1",
                file=sys.stderr,
                flush=True,
            )
    else:
        reason = "--no-run-refactor-pass-1_2" if not args.run_refactor_pass_1_2 else "pass 1 preview unavailable"
        print(f"[pipeline] refactor-pass-1_2: skipped ({reason})", file=sys.stderr, flush=True)

    if args.run_refactor_pass_1_3 and can_run_pass_1_3:
        proof_retarget_result = run_stage(
            "refactor-pass-1_3",
            proof_retarget_cmd,
            dry_run=args.dry_run,
            capture_output=True,
        )
        if proof_retarget_result is None or proof_retarget_result.returncode == 0:
            review_input = args.preview_file
        else:
            print(
                "[pipeline] refactor-pass-1_3 failed; keeping preview input before proof retargeting",
                file=sys.stderr,
                flush=True,
            )
    else:
        reason = "--no-run-refactor-pass-1_3" if not args.run_refactor_pass_1_3 else "pass 1 preview unavailable"
        print(f"[pipeline] refactor-pass-1_3: skipped ({reason})", file=sys.stderr, flush=True)

    if args.run_refactor_pass_1_4 and can_run_pass_1_4:
        presentation_result = run_stage("refactor-pass-1_4", presentation_cmd, dry_run=args.dry_run, capture_output=True)
        if presentation_result is None or presentation_result.returncode == 0:
            review_input = args.preview_file
        else:
            print(
                "[pipeline] refactor-pass-1_4 failed; keeping preview input before presentation shaping",
                file=sys.stderr,
                flush=True,
            )
    else:
        reason = "--no-run-refactor-pass-1_4" if not args.run_refactor_pass_1_4 else "pass 1 preview unavailable"
        print(f"[pipeline] refactor-pass-1_4: skipped ({reason})", file=sys.stderr, flush=True)

    if args.run_refactor_pass_1_5:
        rewrite_cmd = build_rewrite_command(args, input_file=rewrite_input, output_file=rewrite_output)
        rewrite_result = run_stage("refactor-pass-1_5", rewrite_cmd, dry_run=args.dry_run, capture_output=True)
        if rewrite_result is None or rewrite_result.returncode == 0:
            review_input = rewrite_output
        else:
            print(
                "[pipeline] refactor-pass-1_5 failed; falling back to review input before tryAtEachStep rewrites",
                file=sys.stderr,
                flush=True,
            )
    else:
        print("[pipeline] refactor-pass-1_5: skipped (--no-run-refactor-pass-1_5)", file=sys.stderr, flush=True)

    if args.run_refactor_pass_2:
        review_cmd = build_review_command_with_input(args, input_file=review_input)
        require_success("refactor-pass-2", run_stage("refactor-pass-2", review_cmd, dry_run=args.dry_run))
    else:
        print("[pipeline] refactor-pass-2: skipped (--no-run-refactor-pass-2)", file=sys.stderr, flush=True)

    if args.dry_run:
        print("[pipeline] dry-run only; no stage was executed.", file=sys.stderr, flush=True)
        return 0

    print(
        "Pipeline completed.\n"
        f"- theory: {DEFAULT_THEORY}\n"
        f"- seeds: {DEFAULT_SEEDS}\n"
        f"- derived: {DEFAULT_DERIVED}\n"
        f"- refactor preview: {args.preview_file}\n"
        f"- pass 1.2 plan: {args.compression_plan_file}\n"
        f"- pass 1.2 report: {args.compression_report_file}\n"
        f"- pass 1.3 plan: {args.proof_retarget_plan_file}\n"
        f"- pass 1.3 report: {args.proof_retarget_report_file}\n"
        f"- pass 1.4 plan: {args.presentation_plan_file}\n"
        f"- pass 1.4 report: {args.presentation_report_file}\n"
        f"- pass 1 log: {args.refactor_progress_log_file}\n"
        f"- pass 1.2 log: {args.compression_progress_log_file}\n"
        f"- pass 1.3 log: {args.proof_retarget_progress_log_file}\n"
        f"- pass 1.4 log: {args.presentation_progress_log_file}\n"
        f"- tryAtEachStep raw: {args.try_at_each_step_raw_output_file}\n"
        f"- tryAtEachStep report: {args.try_at_each_step_apply_report_file}\n"
        f"- reviewed output: {args.review_output_file}\n"
        f"- review report: {args.review_report_file}",
        file=sys.stderr,
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
