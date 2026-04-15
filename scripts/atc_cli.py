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


def _append_many_flags(cmd: list[str], flag_values: list[tuple[str, str | int | Path | None]]) -> None:
    for flag, value in flag_values:
        _append_flag(cmd, flag, value)


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


def _add_pipeline_refactor_toggles(parser: argparse.ArgumentParser, *, default: bool | None = None) -> None:
    for flag in (
        "run-seed",
        "run-alpha-dedupe-before-pass-1_5",
        "run-refactor-pass-1_5",
        "run-refactor-pass-2",
    ):
        parser.add_argument(f"--{flag}", action=argparse.BooleanOptionalAction, default=default)


def _add_pipeline_artifact_flags(
    parser: argparse.ArgumentParser,
    *,
    include_review_output_file: bool = False,
) -> None:
    parser.add_argument("--alpha-dedupe-report-file")
    parser.add_argument("--alpha-dedupe-equivalence-mode", choices=("alpha", "defeq"))
    parser.add_argument("--review-report-file")
    parser.add_argument("--try-at-each-step-tactic")
    parser.add_argument("--try-at-each-step-raw-output-file")
    parser.add_argument("--try-at-each-step-apply-report-file")
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
    cmd = _python_command("loop/run_loop.py")
    _append_bool_flag(cmd, "--initialize-on-start", config.runtime.initialize_on_start)
    _append_bool_flag(cmd, "--phase-logs", config.runtime.phase_logs)
    if args.skip_verify:
        cmd.append("--skip-verify")
    _append_flag(cmd, "--max-iterations", config.runtime.max_iterations)
    _append_flag(cmd, "--parallel-sessions", config.runtime.parallel_sessions)
    _append_flag(cmd, "--seed-count", config.runtime.seed_count)
    _append_flag(cmd, "--open-problem-failure-threshold", config.runtime.open_problem_failure_threshold)
    _append_flag(cmd, "--prover-retry-budget-sec", config.runtime.prover_retry_budget_sec)
    _append_flag(cmd, "--formalization-retry-budget-sec", config.runtime.formalization_retry_budget_sec)
    _append_flag(cmd, "--max-same-error-streak", config.runtime.max_same_error_streak)
    return cmd, build_worker_env(config)


def _pipeline_command(args: argparse.Namespace, config: AppConfig) -> tuple[list[str], dict[str, str]]:
    cmd = _python_command("loop/run_pipeline.py")
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
    _append_flag(cmd, "--prover-retry-budget-sec", config.runtime.prover_retry_budget_sec)
    _append_flag(cmd, "--formalization-retry-budget-sec", config.runtime.formalization_retry_budget_sec)
    _append_flag(cmd, "--max-same-error-streak", config.runtime.max_same_error_streak)
    _append_flag(cmd, "--preview-file", args.preview_file or config.paths.preview_file)
    _append_flag(cmd, "--alpha-dedupe-report-file", args.alpha_dedupe_report_file)
    _append_flag(cmd, "--alpha-dedupe-equivalence-mode", args.alpha_dedupe_equivalence_mode)
    _append_flag(cmd, "--review-output-file", args.review_output_file or config.paths.reviewed_file)
    _append_flag(cmd, "--review-report-file", args.review_report_file or config.paths.review_report_file)
    _append_flag(
        cmd,
        "--try-at-each-step-raw-output-file",
        args.try_at_each_step_raw_output_file,
    )
    _append_flag(
        cmd,
        "--try-at-each-step-apply-report-file",
        args.try_at_each_step_apply_report_file,
    )
    _append_flag(
        cmd,
        "--try-at-each-step-tactic",
        args.try_at_each_step_tactic or config.runtime.try_at_each_step_tactic,
    )
    _append_flag(cmd, "--review-model", args.review_model)
    _append_flag(cmd, "--review-sandbox", args.review_sandbox)
    _append_bool_flag(cmd, "--run-seed", config.runtime.run_seed)
    if args.run_alpha_dedupe_before_pass_1_5 is not None:
        _append_bool_flag(cmd, "--run-alpha-dedupe-before-pass-1_5", args.run_alpha_dedupe_before_pass_1_5)
    _append_bool_flag(cmd, "--run-refactor-pass-1_5", config.runtime.run_refactor_pass_1_5)
    _append_bool_flag(cmd, "--run-refactor-pass-2", config.runtime.run_refactor_pass_2)
    if args.no_review_verify:
        cmd.append("--no-review-verify")
    return cmd, build_worker_env(config)


def _cycle_command(args: argparse.Namespace, config: AppConfig) -> tuple[list[str], dict[str, str]]:
    cmd = _python_command("loop/run_cycle.py")
    _append_many_flags(
        cmd,
        [
            ("--worker-command", args.worker_command),
            ("--worker-timeout", args.worker_timeout),
            ("--theory-file", args.theory_file or config.paths.theory_file),
            ("--derived-file", args.derived_file or config.paths.derived_file),
            ("--scratch-file", args.scratch_file or config.paths.scratch_file),
            ("--data-dir", args.data_dir or config.paths.data_dir),
            ("--phase-attempts-file", args.phase_attempts_file),
            ("--snapshot-root", args.snapshot_root or config.paths.snapshot_root),
            (
                "--cycle-iterations",
                args.cycle_iterations if args.cycle_iterations is not None else config.runtime.cycle_iterations,
            ),
            ("--parallel-sessions", config.runtime.parallel_sessions),
            ("--seed-count", config.runtime.seed_count),
            ("--open-problem-failure-threshold", config.runtime.open_problem_failure_threshold),
            ("--prover-retry-budget-sec", config.runtime.prover_retry_budget_sec),
            ("--paper-claim-retry-budget-sec", config.runtime.formalization_retry_budget_sec),
            ("--max-same-error-streak", config.runtime.max_same_error_streak),
            ("--batch-generator-open-target-min", args.batch_generator_open_target_min),
        ],
    )
    _append_bool_flag(
        cmd,
        "--phase-logs",
        config.runtime.phase_logs if args.phase_logs is None else args.phase_logs,
    )
    _append_bool_flag(
        cmd,
        "--initialize-on-start",
        bool(args.initialize_on_start),
    )
    if args.skip_verify:
        cmd.append("--skip-verify")
    return cmd, build_worker_env(config)


def _paper_claim_command(args: argparse.Namespace, config: AppConfig) -> tuple[list[str], dict[str, str]]:
    cmd = _python_command("paper_claim/run_paper_claim_session.py")
    cmd.append("--enable-worker")
    open_problem_failure_threshold = (
        args.open_problem_failure_threshold
        if args.open_problem_failure_threshold is not None
        else config.runtime.open_problem_failure_threshold
    )
    batch_generator_seed_count = (
        args.batch_generator_seed_count if args.batch_generator_seed_count is not None else config.runtime.seed_count
    )
    _append_flag(cmd, "--theory-file", args.theory_file or config.paths.theory_file)
    _append_flag(cmd, "--derived-file", args.derived_file or config.paths.derived_file)
    _append_flag(cmd, "--scratch-file", args.scratch_file or config.paths.scratch_file)
    _append_flag(cmd, "--data-dir", args.data_dir or config.paths.data_dir)
    _append_flag(
        cmd,
        "--phase-attempts-file",
        args.phase_attempts_file,
    )
    _append_flag(cmd, "--session-events-file", getattr(args, "session_events_file", None))
    _append_flag(cmd, "--resume-from-session-events-file", getattr(args, "resume_from_session_events_file", None))
    _append_flag(cmd, "--resume-plan-id", getattr(args, "resume_plan_id", None))
    _append_flag(cmd, "--run-id", args.run_id)
    _append_flag(cmd, "--current-iteration", args.current_iteration)
    _append_bool_flag(
        cmd,
        "--phase-logs",
        config.runtime.phase_logs if args.phase_logs is None else args.phase_logs,
    )
    if args.skip_verify:
        cmd.append("--skip-verify")
    _append_flag(cmd, "--verify-timeout", args.verify_timeout)
    _append_flag(
        cmd,
        "--paper-claim-retry-budget-sec",
        args.paper_claim_retry_budget_sec if args.paper_claim_retry_budget_sec is not None else config.runtime.formalization_retry_budget_sec,
    )
    _append_flag(cmd, "--open-problem-failure-threshold", open_problem_failure_threshold)
    _append_flag(cmd, "--batch-generator-seed-count", batch_generator_seed_count)
    _append_flag(cmd, "--batch-generator-open-target-min", args.batch_generator_open_target_min)
    return cmd, build_worker_env(config)


def _review_command(args: argparse.Namespace, config: AppConfig) -> tuple[list[str], dict[str, str]]:
    cmd = _python_command("refactor/direct_refactor_derived.py")
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
    cmd = _python_command("refactor/apply_try_at_each_step_rewrites.py")
    cmd.extend(
        [
            "--input-file",
            str(input_file),
            "--output-file",
            str(output_file),
            "--tactic",
            str(args.tactic or config.runtime.try_at_each_step_tactic),
        ]
    )
    _append_flag(cmd, "--raw-output-file", args.raw_output_file)
    _append_flag(cmd, "--apply-report-file", args.apply_report_file)
    _append_flag(cmd, "--backup-file", args.backup_file)
    _append_flag(cmd, "--verify-timeout", args.verify_timeout)
    if args.dry_run:
        cmd.append("--dry-run")
    return cmd, {}


def _extract_derived_deps_command(args: argparse.Namespace, config: AppConfig) -> tuple[list[str], dict[str, str]]:
    cmd = _python_command("refactor/extract_derived_dependencies.py")
    _append_flag(cmd, "--derived-file", getattr(args, "derived_file", None) or config.paths.derived_file)
    _append_flag(cmd, "--output-file", args.output_file)
    _append_flag(cmd, "--extractor-file", args.extractor_file)
    _append_flag(cmd, "--build-target", args.build_target)
    _append_flag(cmd, "--depth", args.depth)
    return cmd, {}


def _research_agenda_command(args: argparse.Namespace, config: AppConfig) -> tuple[list[str], dict[str, str]]:
    cmd = _python_command("generate_research_agenda_from_report.py")
    _append_flag(cmd, "--report-file", args.report_file)
    _append_flag(cmd, "--output-file", args.output_file or REPO_ROOT / "AutomatedTheoryConstruction" / "research_agenda.md")
    _append_flag(cmd, "--system-prompt-file", args.system_prompt_file)
    _append_flag(cmd, "--user-prompt-file", args.user_prompt_file)
    _append_flag(cmd, "--title", args.title)
    _append_flag(cmd, "--field", args.field)
    _append_flag(cmd, "--style-anchor-file", args.style_anchor_file)
    for item in args.local_preference:
        cmd.extend(["--local-preference", item])
    _append_flag(cmd, "--provider", args.provider)
    _append_flag(cmd, "--model", args.model)
    _append_flag(cmd, "--sandbox", args.sandbox)
    _append_flag(cmd, "--timeout-sec", args.timeout_sec)
    _append_flag(cmd, "--prompt-output-file", args.prompt_output_file)
    if args.preview_prompt:
        cmd.append("--preview-prompt")
    if args.print_output:
        cmd.append("--print-output")
    return cmd, {}


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Unified CLI for the ATC runtime scripts.")
    subparsers = parser.add_subparsers(dest="command", required=True)
    verify_timeout_help = "Per Lean verification timeout in seconds."

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

    cycle = subparsers.add_parser("cycle", help="Run one cycle: loop -> paper claim -> refactor -> snapshot.")
    _add_common_flags(cycle)
    _add_worker_flags(cycle, include_refactor_task=True)
    _add_loop_task_worker_flags(cycle)
    cycle.add_argument("--theory-file")
    cycle.add_argument("--derived-file")
    cycle.add_argument("--scratch-file")
    cycle.add_argument("--data-dir")
    cycle.add_argument("--phase-attempts-file")
    cycle.add_argument("--snapshot-root")
    cycle.add_argument("--cycle-iterations", type=int)
    cycle.add_argument("--skip-verify", action="store_true")
    cycle.add_argument("--initialize-on-start", action=argparse.BooleanOptionalAction, default=None)
    cycle.add_argument("--phase-logs", action=argparse.BooleanOptionalAction, default=None)
    cycle.add_argument("--batch-generator-open-target-min", type=int, default=2)

    pipeline = subparsers.add_parser("pipeline", help="Run seed -> loop -> preview copy -> alpha-dedupe -> rewrite -> review.")
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
    pipeline.add_argument("--preview-file")
    _add_pipeline_artifact_flags(pipeline, include_review_output_file=True)
    _add_review_flags(pipeline)
    _add_pipeline_refactor_toggles(pipeline, default=None)

    def _add_paper_claim_parser(name: str, help_text: str) -> None:
        parser = subparsers.add_parser(name, help=help_text)
        _add_common_flags(parser)
        _add_worker_flags(parser)
        _add_loop_task_worker_flags(parser)
        parser.add_argument("--theory-file")
        parser.add_argument("--derived-file")
        parser.add_argument("--scratch-file")
        parser.add_argument("--data-dir")
        parser.add_argument("--phase-attempts-file")
        parser.add_argument("--session-events-file")
        parser.add_argument("--resume-from-session-events-file")
        parser.add_argument("--resume-plan-id")
        parser.add_argument("--run-id")
        parser.add_argument("--current-iteration", type=int)
        parser.add_argument("--phase-logs", action=argparse.BooleanOptionalAction, default=None)
        parser.add_argument("--skip-verify", action="store_true")
        parser.add_argument("--verify-timeout", type=int)
        parser.add_argument("--paper-claim-retry-budget-sec", type=int)
        parser.add_argument("--open-problem-failure-threshold", type=int)
        parser.add_argument("--batch-generator-seed-count", type=int)
        parser.add_argument("--batch-generator-open-target-min", type=int)

    _add_paper_claim_parser("paper-claim", "Run a one-shot paper claim session.")

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

    extract_deps = subparsers.add_parser(
        "extract-derived-deps",
        help="Refresh data/refactor/derived-deps.json from DependencyExtractor.lean and Derived.lean.",
    )
    _add_common_flags(extract_deps)
    extract_deps.add_argument("--derived-file")
    extract_deps.add_argument("--output-file")
    extract_deps.add_argument("--extractor-file")
    extract_deps.add_argument("--build-target", default="AutomatedTheoryConstruction.Derived")
    extract_deps.add_argument("--depth", type=int, default=1)

    research_agenda = subparsers.add_parser(
        "research-agenda",
        help="Generate AutomatedTheoryConstruction/research_agenda.md from a deep-research report.",
    )
    _add_common_flags(research_agenda)
    research_agenda.add_argument("--report-file", required=True)
    research_agenda.add_argument("--output-file")
    research_agenda.add_argument("--system-prompt-file")
    research_agenda.add_argument("--user-prompt-file")
    research_agenda.add_argument("--title")
    research_agenda.add_argument("--field")
    research_agenda.add_argument("--style-anchor-file")
    research_agenda.add_argument("--local-preference", action="append", default=[])
    research_agenda.add_argument("--provider")
    research_agenda.add_argument("--model")
    research_agenda.add_argument("--sandbox", default="read-only")
    research_agenda.add_argument("--timeout-sec", type=int)
    research_agenda.add_argument("--prompt-output-file")
    research_agenda.add_argument("--preview-prompt", action="store_true")
    research_agenda.add_argument("--print-output", action="store_true")

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
    _add_pipeline_artifact_flags(config_show, include_review_output_file=False)

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
        "cycle": _cycle_command,
        "pipeline": _pipeline_command,
        "paper-claim": _paper_claim_command,
        "rewrite": _rewrite_command,
        "review": _review_command,
        "extract-derived-deps": _extract_derived_deps_command,
        "research-agenda": _research_agenda_command,
    }
    builder = builders[args.command]

    cmd, env_updates = builder(args, config)
    return _run_command(cmd, env_updates=env_updates, dry_run=bool(args.dry_run))


if __name__ == "__main__":
    raise SystemExit(main())
