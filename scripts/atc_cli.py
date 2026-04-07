from __future__ import annotations

import argparse
import os
import shlex
import subprocess
import sys
from pathlib import Path

from atc_config import REPO_ROOT
from atc_config import AppConfig
from atc_config import app_config_to_json
from atc_config import build_worker_env
from atc_config import load_app_config


def _script_path(name: str) -> str:
    return str((REPO_ROOT / "scripts" / name).resolve())


def _python_command(script_name: str) -> list[str]:
    return [sys.executable, _script_path(script_name)]


def _append_flag(cmd: list[str], flag: str, value: str | int | Path | None) -> None:
    if value is None:
        return
    if isinstance(value, str) and value == "":
        return
    cmd.extend([flag, str(value)])


def _append_bool_flag(cmd: list[str], flag: str, enabled: bool) -> None:
    cmd.append(flag if enabled else f"--no-{flag.removeprefix('--')}")


def _run_command(cmd: list[str], *, env_updates: dict[str, str], dry_run: bool) -> int:
    env = os.environ.copy()
    env.update(env_updates)

    if env_updates:
        pairs = [f"{key}={shlex.quote(value)}" for key, value in sorted(env_updates.items())]
        print(f"[atc] env: {' '.join(pairs)}", file=sys.stderr, flush=True)
    print(f"[atc] exec: {shlex.join(cmd)}", file=sys.stderr, flush=True)

    if dry_run:
        return 0

    completed = subprocess.run(
        cmd,
        cwd=str(REPO_ROOT),
        env=env,
        check=False,
    )
    return completed.returncode


def _add_common_flags(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--config")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--log-format", choices=("pretty", "json"))
    parser.add_argument("--log-level", choices=("debug", "info", "warning", "error"))
    parser.add_argument("--log-worker-raw", action=argparse.BooleanOptionalAction, default=None)


def _add_worker_flags(parser: argparse.ArgumentParser, *, include_refactor_task: bool = False) -> None:
    parser.add_argument("--worker-command")
    parser.add_argument("--worker-timeout", type=int)
    parser.add_argument("--codex-model")
    parser.add_argument("--codex-timeout", type=int)
    if include_refactor_task:
        parser.add_argument("--refactor-worker-command")
        parser.add_argument("--refactor-worker-timeout", type=int)
        parser.add_argument("--refactor-codex-model")
        parser.add_argument("--refactor-codex-timeout", type=int)


def _add_loop_task_worker_flags(parser: argparse.ArgumentParser) -> None:
    task_prefixes = (
        "prover",
        "prover_statement",
        "formalize",
        "repair",
        "prioritize_open_problems",
    )
    for prefix in task_prefixes:
        parser.add_argument(f"--{prefix.replace('_', '-')}-worker-command", dest=f"{prefix}_worker_command")
        parser.add_argument(f"--{prefix.replace('_', '-')}-worker-timeout", dest=f"{prefix}_worker_timeout", type=int)
        parser.add_argument(f"--{prefix.replace('_', '-')}-codex-model", dest=f"{prefix}_codex_model")
        parser.add_argument(f"--{prefix.replace('_', '-')}-codex-timeout", dest=f"{prefix}_codex_timeout", type=int)


def _add_initialize_phase_flags(parser: argparse.ArgumentParser, *, default: bool | None = None) -> None:
    parser.add_argument("--initialize-on-start", action=argparse.BooleanOptionalAction, default=default)
    parser.add_argument("--phase-logs", action=argparse.BooleanOptionalAction, default=default)


def _add_loop_tuning_flags(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--max-iterations", type=int)
    parser.add_argument("--parallel-sessions", type=int)
    parser.add_argument("--open-problem-failure-threshold", type=int)
    parser.add_argument("--prover-retry-budget-sec", type=int, help="Whole retry-loop budget in seconds.")
    parser.add_argument("--formalization-retry-budget-sec", type=int, help="Whole retry-loop budget in seconds.")
    parser.add_argument("--max-same-error-streak", type=int)
    parser.add_argument("--priority-refresh-theorem-interval", type=int)
    parser.add_argument("--main-theorem-interval", type=int)
    parser.add_argument("--main-theorem-formalize-worker-timeout", type=int, help="Per worker subprocess timeout in seconds.")
    parser.add_argument("--main-theorem-repair-worker-timeout", type=int, help="Per worker subprocess timeout in seconds.")
    parser.add_argument("--main-theorem-verify-timeout", type=int, help="Per Lean verification timeout in seconds.")
    parser.add_argument(
        "--main-theorem-formalization-retry-budget-sec", type=int, help="Whole retry-loop budget in seconds."
    )


def _add_pipeline_refactor_toggles(parser: argparse.ArgumentParser, *, default: bool | None = None) -> None:
    for flag in (
        "run-seed",
        "run-refactor-pass-1",
        "run-refactor-pass-1_2",
        "run-refactor-pass-1_3",
        "run-refactor-pass-1_4",
        "run-refactor-pass-1_5",
        "run-refactor-pass-2",
        "run-main-theorem-session",
    ):
        parser.add_argument(f"--{flag}", action=argparse.BooleanOptionalAction, default=default)


def _add_budget_flags(
    parser: argparse.ArgumentParser,
    *,
    refactor_help: str,
    compression_help: str,
    proof_retarget_help: str,
    presentation_help: str,
) -> None:
    parser.add_argument("--refactor-max-wall-clock-sec", type=int, help=refactor_help)
    parser.add_argument("--compression-max-wall-clock-sec", type=int, help=compression_help)
    parser.add_argument("--proof-retarget-max-wall-clock-sec", type=int, help=proof_retarget_help)
    parser.add_argument("--presentation-max-wall-clock-sec", type=int, help=presentation_help)


def _add_pipeline_artifact_flags(
    parser: argparse.ArgumentParser,
    *,
    include_review_output_file: bool = False,
    include_theorem_reuse_memory: bool = False,
) -> None:
    parser.add_argument("--compression-plan-file")
    parser.add_argument("--compression-report-file")
    parser.add_argument("--proof-retarget-plan-file")
    parser.add_argument("--proof-retarget-report-file")
    parser.add_argument("--presentation-plan-file")
    parser.add_argument("--presentation-report-file")
    parser.add_argument("--refactor-progress-log-file")
    parser.add_argument("--compression-progress-log-file")
    parser.add_argument("--proof-retarget-progress-log-file")
    parser.add_argument("--presentation-progress-log-file")
    parser.add_argument("--review-report-file")
    parser.add_argument("--try-at-each-step-tactic")
    parser.add_argument("--try-at-each-step-raw-output-file")
    parser.add_argument("--try-at-each-step-apply-report-file")
    if include_theorem_reuse_memory:
        parser.add_argument("--theorem-reuse-memory-file")
    if include_review_output_file:
        parser.add_argument("--review-output-file")


def _add_review_flags(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--review-model")
    parser.add_argument("--review-sandbox", default="workspace-write")
    parser.add_argument("--no-review-verify", action="store_true")


def _seed_command(args: argparse.Namespace, config: AppConfig) -> tuple[list[str], dict[str, str]]:
    cmd = _python_command("generate_seeds_from_theory.py")
    cmd.extend(
        [
            "--theory-file",
            str(config.paths.theory_file),
            "--derived-file",
            str(config.paths.derived_file),
            "--output-file",
            str(config.paths.seeds_file),
            "--seed-count",
            str(config.runtime.seed_count),
            "--seed-src",
            args.seed_src,
            "--sandbox",
            args.seed_sandbox,
        ]
    )
    if args.seed_extra_instruction:
        _append_flag(cmd, "--extra-instruction", args.seed_extra_instruction)
    _append_flag(cmd, "--model", args.seed_model)
    if args.initialize_runtime_state is False:
        cmd.append("--no-initialize-runtime-state")
    for path in args.context_file:
        cmd.extend(["--context-file", path])
    return cmd, {}


def _loop_command(args: argparse.Namespace, config: AppConfig) -> tuple[list[str], dict[str, str]]:
    cmd = _python_command("run_loop.py")
    _append_bool_flag(cmd, "--initialize-on-start", config.runtime.initialize_on_start)
    _append_bool_flag(cmd, "--phase-logs", config.runtime.phase_logs)
    if args.skip_verify:
        cmd.append("--skip-verify")
    _append_flag(cmd, "--max-iterations", config.runtime.max_iterations)
    _append_flag(cmd, "--parallel-sessions", config.runtime.parallel_sessions)
    _append_flag(cmd, "--open-problem-failure-threshold", config.runtime.open_problem_failure_threshold)
    _append_flag(cmd, "--prover-retry-budget-sec", config.runtime.prover_retry_budget_sec)
    _append_flag(cmd, "--formalization-retry-budget-sec", config.runtime.formalization_retry_budget_sec)
    _append_flag(cmd, "--max-same-error-streak", config.runtime.max_same_error_streak)
    _append_flag(cmd, "--priority-refresh-theorem-interval", config.runtime.priority_refresh_theorem_interval)
    if config.runtime.run_main_theorem_session:
        _append_flag(cmd, "--main-theorem-interval", config.runtime.main_theorem_interval)
    else:
        cmd.extend(["--main-theorem-interval", "0"])
    _append_flag(
        cmd,
        "--main-theorem-formalize-worker-timeout",
        config.runtime.main_theorem_formalize_worker_timeout,
    )
    _append_flag(
        cmd,
        "--main-theorem-repair-worker-timeout",
        config.runtime.main_theorem_repair_worker_timeout,
    )
    _append_flag(cmd, "--main-theorem-verify-timeout", config.runtime.main_theorem_verify_timeout)
    _append_flag(
        cmd,
        "--main-theorem-formalization-retry-budget-sec",
        config.runtime.main_theorem_formalization_retry_budget_sec,
    )
    return cmd, build_worker_env(config)


def _pipeline_command(args: argparse.Namespace, config: AppConfig) -> tuple[list[str], dict[str, str]]:
    cmd = _python_command("run_pipeline.py")
    for path in args.context_file:
        cmd.extend(["--context-file", path])
    _append_flag(cmd, "--seed-count", config.runtime.seed_count)
    _append_flag(cmd, "--seed-src", args.seed_src)
    _append_flag(cmd, "--seed-extra-instruction", args.seed_extra_instruction)
    _append_flag(cmd, "--seed-model", args.seed_model)
    _append_flag(cmd, "--seed-sandbox", args.seed_sandbox)
    _append_bool_flag(cmd, "--initialize-on-start", config.runtime.initialize_on_start)
    _append_bool_flag(cmd, "--phase-logs", config.runtime.phase_logs)
    if args.skip_loop_verify:
        cmd.append("--skip-loop-verify")
    _append_flag(cmd, "--max-iterations", config.runtime.max_iterations)
    _append_flag(cmd, "--parallel-sessions", config.runtime.parallel_sessions)
    _append_flag(cmd, "--open-problem-failure-threshold", config.runtime.open_problem_failure_threshold)
    _append_flag(cmd, "--refactor-max-wall-clock-sec", config.runtime.refactor_pass_1_max_wall_clock_sec)
    _append_flag(cmd, "--compression-max-wall-clock-sec", config.runtime.refactor_pass_1_2_max_wall_clock_sec)
    _append_flag(cmd, "--proof-retarget-max-wall-clock-sec", config.runtime.refactor_pass_1_3_max_wall_clock_sec)
    _append_flag(cmd, "--presentation-max-wall-clock-sec", config.runtime.refactor_pass_1_4_max_wall_clock_sec)
    _append_flag(cmd, "--prover-retry-budget-sec", config.runtime.prover_retry_budget_sec)
    _append_flag(cmd, "--formalization-retry-budget-sec", config.runtime.formalization_retry_budget_sec)
    _append_flag(cmd, "--max-same-error-streak", config.runtime.max_same_error_streak)
    _append_flag(cmd, "--priority-refresh-theorem-interval", config.runtime.priority_refresh_theorem_interval)
    _append_flag(cmd, "--main-theorem-interval", config.runtime.main_theorem_interval)
    _append_flag(
        cmd,
        "--main-theorem-formalize-worker-timeout",
        config.runtime.main_theorem_formalize_worker_timeout,
    )
    _append_flag(
        cmd,
        "--main-theorem-repair-worker-timeout",
        config.runtime.main_theorem_repair_worker_timeout,
    )
    _append_flag(cmd, "--main-theorem-verify-timeout", config.runtime.main_theorem_verify_timeout)
    _append_flag(
        cmd,
        "--main-theorem-formalization-retry-budget-sec",
        config.runtime.main_theorem_formalization_retry_budget_sec,
    )
    _append_flag(cmd, "--preview-file", args.preview_file or config.paths.preview_file)
    _append_flag(
        cmd,
        "--compression-plan-file",
        args.compression_plan_file or config.paths.compression_plan_file,
    )
    _append_flag(
        cmd,
        "--compression-report-file",
        args.compression_report_file or config.paths.compression_report_file,
    )
    _append_flag(
        cmd,
        "--refactor-progress-log-file",
        args.refactor_progress_log_file or config.paths.refactor_pass_1_log_file,
    )
    _append_flag(
        cmd,
        "--compression-progress-log-file",
        args.compression_progress_log_file or config.paths.compression_executor_log_file,
    )
    _append_flag(
        cmd,
        "--proof-retarget-plan-file",
        args.proof_retarget_plan_file or config.paths.proof_retarget_plan_file,
    )
    _append_flag(
        cmd,
        "--proof-retarget-report-file",
        args.proof_retarget_report_file or config.paths.proof_retarget_report_file,
    )
    _append_flag(
        cmd,
        "--proof-retarget-progress-log-file",
        args.proof_retarget_progress_log_file or config.paths.proof_retarget_executor_log_file,
    )
    _append_flag(
        cmd,
        "--presentation-plan-file",
        args.presentation_plan_file or config.paths.presentation_plan_file,
    )
    _append_flag(
        cmd,
        "--presentation-report-file",
        args.presentation_report_file or config.paths.presentation_report_file,
    )
    _append_flag(
        cmd,
        "--presentation-progress-log-file",
        args.presentation_progress_log_file or config.paths.presentation_executor_log_file,
    )
    _append_flag(cmd, "--review-output-file", args.review_output_file or config.paths.reviewed_file)
    _append_flag(cmd, "--review-report-file", args.review_report_file or config.paths.review_report_file)
    _append_flag(
        cmd,
        "--try-at-each-step-raw-output-file",
        args.try_at_each_step_raw_output_file or config.paths.try_at_each_step_raw_output_file,
    )
    _append_flag(
        cmd,
        "--try-at-each-step-apply-report-file",
        args.try_at_each_step_apply_report_file or config.paths.try_at_each_step_apply_report_file,
    )
    _append_flag(
        cmd,
        "--try-at-each-step-tactic",
        args.try_at_each_step_tactic or config.runtime.try_at_each_step_tactic,
    )
    _append_flag(cmd, "--review-model", args.review_model)
    _append_flag(cmd, "--review-sandbox", args.review_sandbox)
    _append_bool_flag(cmd, "--run-seed", config.runtime.run_seed)
    _append_bool_flag(cmd, "--run-refactor-pass-1", config.runtime.run_refactor_pass_1)
    _append_bool_flag(cmd, "--run-refactor-pass-1_2", config.runtime.run_refactor_pass_1_2)
    _append_bool_flag(cmd, "--run-refactor-pass-1_3", config.runtime.run_refactor_pass_1_3)
    _append_bool_flag(cmd, "--run-refactor-pass-1_4", config.runtime.run_refactor_pass_1_4)
    _append_bool_flag(cmd, "--run-refactor-pass-1_5", config.runtime.run_refactor_pass_1_5)
    _append_bool_flag(cmd, "--run-refactor-pass-2", config.runtime.run_refactor_pass_2)
    _append_bool_flag(cmd, "--run-main-theorem-session", config.runtime.run_main_theorem_session)
    if args.no_review_verify:
        cmd.append("--no-review-verify")
    return cmd, build_worker_env(config)


def _refactor_command(args: argparse.Namespace, config: AppConfig) -> tuple[list[str], dict[str, str]]:
    cmd = _python_command("refactor_derived.py")
    cmd.extend(
        [
            "--derived-file",
            str(config.paths.derived_file),
            "--theory-file",
            str(config.paths.theory_file),
            "--theorem-reuse-memory-file",
            str(config.paths.theorem_reuse_memory_file),
        ]
    )
    _append_flag(cmd, "--prompt-file", args.prompt_file)
    _append_flag(cmd, "--verify-timeout", args.verify_timeout)
    _append_flag(cmd, "--max-wall-clock-sec", config.runtime.refactor_pass_1_max_wall_clock_sec)
    if args.apply:
        cmd.append("--apply")
    _append_flag(cmd, "--output-file", args.output_file or (None if args.apply else config.paths.preview_file))
    _append_flag(cmd, "--backup-file", args.backup_file)
    _append_flag(cmd, "--progress-log-file", args.refactor_progress_log_file or config.paths.refactor_pass_1_log_file)
    return cmd, build_worker_env(config, task_names=("refactor_derived",))


def _compress_command(args: argparse.Namespace, config: AppConfig) -> tuple[list[str], dict[str, str]]:
    input_file = getattr(args, "input_file", None) or config.paths.preview_file
    output_file = getattr(args, "output_file", None) or input_file
    compression_plan_file = getattr(args, "compression_plan_file", None) or config.paths.compression_plan_file
    compression_report_file = getattr(args, "compression_report_file", None) or config.paths.compression_report_file
    compression_progress_log_file = (
        getattr(args, "compression_progress_log_file", None) or config.paths.compression_executor_log_file
    )
    theorem_reuse_memory_file = (
        getattr(args, "theorem_reuse_memory_file", None) or config.paths.theorem_reuse_memory_file
    )
    cmd = _python_command("run_compression_pass.py")
    cmd.extend(
        [
            "--input-file",
            str(input_file),
            "--theory-file",
            str(config.paths.theory_file),
            "--plan-file",
            str(compression_plan_file),
            "--report-file",
            str(compression_report_file),
            "--progress-log-file",
            str(compression_progress_log_file),
            "--theorem-reuse-memory-file",
            str(theorem_reuse_memory_file),
        ]
    )
    _append_flag(cmd, "--output-file", output_file)
    _append_flag(cmd, "--planner-prompt-file", getattr(args, "planner_prompt_file", None))
    _append_flag(cmd, "--executor-prompt-file", getattr(args, "executor_prompt_file", None))
    _append_flag(cmd, "--verify-timeout", getattr(args, "verify_timeout", None))
    _append_flag(cmd, "--max-wall-clock-sec", config.runtime.refactor_pass_1_2_max_wall_clock_sec)
    return cmd, build_worker_env(config, task_names=("refactor_derived",))


def _retarget_command(args: argparse.Namespace, config: AppConfig) -> tuple[list[str], dict[str, str]]:
    input_file = getattr(args, "input_file", None) or config.paths.preview_file
    output_file = getattr(args, "output_file", None) or input_file
    proof_retarget_plan_file = (
        getattr(args, "proof_retarget_plan_file", None) or config.paths.proof_retarget_plan_file
    )
    proof_retarget_report_file = (
        getattr(args, "proof_retarget_report_file", None) or config.paths.proof_retarget_report_file
    )
    proof_retarget_progress_log_file = (
        getattr(args, "proof_retarget_progress_log_file", None) or config.paths.proof_retarget_executor_log_file
    )
    theorem_reuse_memory_file = (
        getattr(args, "theorem_reuse_memory_file", None) or config.paths.theorem_reuse_memory_file
    )
    cmd = _python_command("run_proof_retarget_pass.py")
    cmd.extend(
        [
            "--input-file",
            str(input_file),
            "--theory-file",
            str(config.paths.theory_file),
            "--plan-file",
            str(proof_retarget_plan_file),
            "--report-file",
            str(proof_retarget_report_file),
            "--progress-log-file",
            str(proof_retarget_progress_log_file),
            "--theorem-reuse-memory-file",
            str(theorem_reuse_memory_file),
        ]
    )
    _append_flag(cmd, "--output-file", output_file)
    _append_flag(cmd, "--planner-prompt-file", getattr(args, "planner_prompt_file", None))
    _append_flag(cmd, "--executor-prompt-file", getattr(args, "executor_prompt_file", None))
    _append_flag(cmd, "--verify-timeout", getattr(args, "verify_timeout", None))
    _append_flag(cmd, "--max-wall-clock-sec", config.runtime.refactor_pass_1_3_max_wall_clock_sec)
    return cmd, build_worker_env(config, task_names=("refactor_derived",))


def _present_command(args: argparse.Namespace, config: AppConfig) -> tuple[list[str], dict[str, str]]:
    input_file = getattr(args, "input_file", None) or config.paths.preview_file
    output_file = getattr(args, "output_file", None) or input_file
    presentation_plan_file = getattr(args, "presentation_plan_file", None) or config.paths.presentation_plan_file
    presentation_report_file = getattr(args, "presentation_report_file", None) or config.paths.presentation_report_file
    presentation_progress_log_file = (
        getattr(args, "presentation_progress_log_file", None) or config.paths.presentation_executor_log_file
    )
    theorem_reuse_memory_file = (
        getattr(args, "theorem_reuse_memory_file", None) or config.paths.theorem_reuse_memory_file
    )
    cmd = _python_command("run_presentation_pass.py")
    cmd.extend(
        [
            "--input-file",
            str(input_file),
            "--theory-file",
            str(config.paths.theory_file),
            "--plan-file",
            str(presentation_plan_file),
            "--report-file",
            str(presentation_report_file),
            "--progress-log-file",
            str(presentation_progress_log_file),
            "--theorem-reuse-memory-file",
            str(theorem_reuse_memory_file),
        ]
    )
    _append_flag(cmd, "--output-file", output_file)
    _append_flag(cmd, "--planner-prompt-file", getattr(args, "planner_prompt_file", None))
    _append_flag(cmd, "--executor-prompt-file", getattr(args, "executor_prompt_file", None))
    _append_flag(cmd, "--verify-timeout", getattr(args, "verify_timeout", None))
    _append_flag(cmd, "--max-wall-clock-sec", config.runtime.refactor_pass_1_4_max_wall_clock_sec)
    return cmd, build_worker_env(config, task_names=("refactor_derived",))


def _review_command(args: argparse.Namespace, config: AppConfig) -> tuple[list[str], dict[str, str]]:
    cmd = _python_command("direct_refactor_derived.py")
    cmd.extend(
        [
            "--input-file",
            str(args.input_file or config.paths.preview_file),
            "--output-file",
            str(args.output_file or config.paths.reviewed_file),
            "--report-file",
            str(args.review_report_file or config.paths.review_report_file),
            "--sandbox",
            args.sandbox,
        ]
    )
    _append_flag(cmd, "--model", args.model)
    _append_flag(cmd, "--policy-file", args.policy_file)
    _append_flag(cmd, "--lean-rule-file", args.lean_rule_file)
    _append_flag(cmd, "--mathlib-usage-file", args.mathlib_usage_file)
    if args.skip_copy:
        cmd.append("--skip-copy")
    if args.no_verify:
        cmd.append("--no-verify")
    return cmd, {}


def _rewrite_command(args: argparse.Namespace, config: AppConfig) -> tuple[list[str], dict[str, str]]:
    input_file = args.input_file or config.paths.preview_file
    output_file = args.output_file or input_file
    cmd = _python_command("apply_try_at_each_step_rewrites.py")
    cmd.extend(
        [
            "--input-file",
            str(input_file),
            "--output-file",
            str(output_file),
            "--raw-output-file",
            str(args.raw_output_file or config.paths.try_at_each_step_raw_output_file),
            "--apply-report-file",
            str(args.apply_report_file or config.paths.try_at_each_step_apply_report_file),
            "--tactic",
            str(args.tactic or config.runtime.try_at_each_step_tactic),
        ]
    )
    _append_flag(cmd, "--backup-file", args.backup_file)
    _append_flag(cmd, "--verify-timeout", args.verify_timeout)
    if args.dry_run:
        cmd.append("--dry-run")
    return cmd, {}


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Unified CLI for the ATC runtime scripts.")
    subparsers = parser.add_subparsers(dest="command", required=True)
    verify_timeout_help = "Per Lean verification timeout in seconds."
    refactor_budget_help = "Whole pass 1 wall-clock budget in seconds."
    compression_budget_help = "Whole pass 1.2 wall-clock budget in seconds."
    proof_retarget_budget_help = "Whole pass 1.3 wall-clock budget in seconds."
    presentation_budget_help = "Whole pass 1.4 wall-clock budget in seconds."

    seed = subparsers.add_parser("seed", help="Generate seeds from the active theory.")
    _add_common_flags(seed)
    seed.add_argument("--theory-file")
    seed.add_argument("--derived-file")
    seed.add_argument("--seeds-file")
    seed.add_argument("--seed-count", type=int)
    seed.add_argument("--seed-src", default="seed")
    seed.add_argument("--seed-extra-instruction", default="")
    seed.add_argument("--seed-model")
    seed.add_argument("--seed-sandbox", default="read-only")
    seed.add_argument("--context-file", action="append", default=[])
    seed.add_argument("--initialize-runtime-state", action=argparse.BooleanOptionalAction, default=None)

    loop = subparsers.add_parser("loop", help="Run the main ATC loop.")
    _add_common_flags(loop)
    _add_worker_flags(loop)
    _add_loop_task_worker_flags(loop)
    loop.add_argument("--skip-verify", action="store_true")
    _add_initialize_phase_flags(loop, default=None)
    _add_loop_tuning_flags(loop)
    loop.add_argument("--run-main-theorem-session", action=argparse.BooleanOptionalAction, default=None)

    pipeline = subparsers.add_parser("pipeline", help="Run seed -> loop -> refactor -> pass 1.2 -> pass 1.3 -> optional pass 1.4 -> rewrite -> review.")
    _add_common_flags(pipeline)
    _add_worker_flags(pipeline, include_refactor_task=True)
    _add_loop_task_worker_flags(pipeline)
    pipeline.add_argument("--seed-count", type=int)
    pipeline.add_argument("--seed-src", default="seed")
    pipeline.add_argument("--seed-extra-instruction", default="")
    pipeline.add_argument("--seed-model")
    pipeline.add_argument("--seed-sandbox", default="read-only")
    pipeline.add_argument("--context-file", action="append", default=[])
    _add_initialize_phase_flags(pipeline, default=None)
    _add_loop_tuning_flags(pipeline)
    pipeline.add_argument("--skip-loop-verify", action="store_true")
    _add_budget_flags(
        pipeline,
        refactor_help=refactor_budget_help,
        compression_help=compression_budget_help,
        proof_retarget_help=proof_retarget_budget_help,
        presentation_help=presentation_budget_help,
    )
    pipeline.add_argument("--preview-file")
    _add_pipeline_artifact_flags(pipeline, include_review_output_file=True, include_theorem_reuse_memory=True)
    _add_review_flags(pipeline)
    _add_pipeline_refactor_toggles(pipeline, default=None)
    refactor = subparsers.add_parser("refactor", help="Run final refactor pass 1 for Derived.lean.")
    _add_common_flags(refactor)
    _add_worker_flags(refactor, include_refactor_task=True)
    refactor.add_argument("--theory-file")
    refactor.add_argument("--derived-file")
    refactor.add_argument("--prompt-file")
    refactor.add_argument("--verify-timeout", type=int, help=verify_timeout_help)
    refactor.add_argument("--output-file")
    refactor.add_argument("--apply", action="store_true")
    refactor.add_argument("--backup-file")
    refactor.add_argument("--progress-log-file", dest="refactor_progress_log_file")
    refactor.add_argument("--max-wall-clock-sec", dest="refactor_max_wall_clock_sec", type=int, help=refactor_budget_help)
    refactor.add_argument("--theorem-reuse-memory-file")

    compress = subparsers.add_parser("compress", help="Run pass 1.2 exact-duplicate collapse on the preview file.")
    _add_common_flags(compress)
    _add_worker_flags(compress, include_refactor_task=True)
    compress.add_argument("--input-file")
    compress.add_argument("--output-file")
    compress.add_argument("--verify-timeout", type=int, help=verify_timeout_help)
    compress.add_argument("--compression-plan-file")
    compress.add_argument("--compression-report-file")
    compress.add_argument("--compression-progress-log-file")
    compress.add_argument("--planner-prompt-file")
    compress.add_argument("--executor-prompt-file")
    compress.add_argument("--theorem-reuse-memory-file")
    compress.add_argument("--max-wall-clock-sec", dest="compression_max_wall_clock_sec", type=int, help=compression_budget_help)

    retarget = subparsers.add_parser("retarget", help="Run pass 1.3 proof retargeting on the preview file.")
    _add_common_flags(retarget)
    _add_worker_flags(retarget, include_refactor_task=True)
    retarget.add_argument("--input-file")
    retarget.add_argument("--output-file")
    retarget.add_argument("--verify-timeout", type=int, help=verify_timeout_help)
    retarget.add_argument("--proof-retarget-plan-file")
    retarget.add_argument("--proof-retarget-report-file")
    retarget.add_argument("--proof-retarget-progress-log-file")
    retarget.add_argument("--planner-prompt-file")
    retarget.add_argument("--executor-prompt-file")
    retarget.add_argument("--theorem-reuse-memory-file")
    retarget.add_argument("--max-wall-clock-sec", dest="proof_retarget_max_wall_clock_sec", type=int, help=proof_retarget_budget_help)

    present = subparsers.add_parser("present", help="Run pass 1.4 presentation shaping on the preview file.")
    _add_common_flags(present)
    _add_worker_flags(present, include_refactor_task=True)
    present.add_argument("--input-file")
    present.add_argument("--output-file")
    present.add_argument("--verify-timeout", type=int, help=verify_timeout_help)
    present.add_argument("--presentation-plan-file")
    present.add_argument("--presentation-report-file")
    present.add_argument("--presentation-progress-log-file")
    present.add_argument("--planner-prompt-file")
    present.add_argument("--executor-prompt-file")
    present.add_argument("--theorem-reuse-memory-file")
    present.add_argument("--max-wall-clock-sec", dest="presentation_max_wall_clock_sec", type=int, help=presentation_budget_help)

    review = subparsers.add_parser("review", help="Run the second review-polish pass.")
    _add_common_flags(review)
    review.add_argument("--input-file")
    review.add_argument("--output-file")
    review.add_argument("--report-file", dest="review_report_file")
    review.add_argument("--model")
    review.add_argument("--sandbox", default="workspace-write")
    review.add_argument("--skip-copy", action="store_true")
    review.add_argument("--no-verify", action="store_true")
    review.add_argument("--policy-file")
    review.add_argument("--lean-rule-file")
    review.add_argument("--mathlib-usage-file")

    rewrite = subparsers.add_parser("rewrite", help="Apply tryAtEachStep rewrites before the review pass.")
    _add_common_flags(rewrite)
    rewrite.add_argument("--input-file")
    rewrite.add_argument("--output-file")
    rewrite.add_argument("--raw-output-file")
    rewrite.add_argument("--apply-report-file")
    rewrite.add_argument("--tactic")
    rewrite.add_argument("--backup-file")
    rewrite.add_argument("--verify-timeout", type=int, help=verify_timeout_help)

    config_cmd = subparsers.add_parser("config", help="Inspect resolved configuration.")
    config_subparsers = config_cmd.add_subparsers(dest="config_command", required=True)
    config_show = config_subparsers.add_parser("show", help="Print resolved config as JSON.")
    _add_common_flags(config_show)
    config_show.add_argument("--theory-file")
    config_show.add_argument("--derived-file")
    config_show.add_argument("--data-dir")
    config_show.add_argument("--log-dir")
    _add_worker_flags(config_show, include_refactor_task=True)
    _add_loop_task_worker_flags(config_show)
    _add_initialize_phase_flags(config_show, default=None)
    config_show.add_argument("--seed-count", type=int)
    _add_loop_tuning_flags(config_show)
    _add_pipeline_refactor_toggles(config_show, default=None)
    _add_pipeline_artifact_flags(config_show, include_review_output_file=False, include_theorem_reuse_memory=False)
    _add_budget_flags(
        config_show,
        refactor_help=refactor_budget_help,
        compression_help=compression_budget_help,
        proof_retarget_help=proof_retarget_budget_help,
        presentation_help=presentation_budget_help,
    )

    return parser


def main() -> int:
    parser = _build_parser()
    args = parser.parse_args()
    try:
        config, sources = load_app_config(args)
    except ValueError as exc:
        print(f"atc_cli.py: error: {exc}", file=sys.stderr, flush=True)
        return 2

    if args.command == "config":
        print(app_config_to_json(config, sources))
        return 0

    builders = {
        "seed": _seed_command,
        "loop": _loop_command,
        "pipeline": _pipeline_command,
        "refactor": _refactor_command,
        "compress": _compress_command,
        "retarget": _retarget_command,
        "present": _present_command,
        "rewrite": _rewrite_command,
        "review": _review_command,
    }
    builder = builders[args.command]

    cmd, env_updates = builder(args, config)
    return _run_command(cmd, env_updates=env_updates, dry_run=bool(args.dry_run))


if __name__ == "__main__":
    raise SystemExit(main())
