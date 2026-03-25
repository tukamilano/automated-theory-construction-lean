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
DEFAULT_REVIEWED = Path("AutomatedTheoryConstruction/Derived.refactored.reviewed.lean")


def append_optional_flag(cmd: list[str], flag: str, value: str | int | None) -> None:
    if value is None:
        return
    text = str(value).strip()
    if not text:
        return
    cmd.extend([flag, text])


def run_stage(name: str, cmd: list[str], *, dry_run: bool) -> None:
    print(f"[pipeline] {name}: {shlex.join(cmd)}", file=sys.stderr, flush=True)
    if dry_run:
        return

    completed = subprocess.run(
        cmd,
        cwd=str(REPO_ROOT),
        check=False,
    )
    if completed.returncode != 0:
        raise SystemExit(completed.returncode)


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
    for path in args.context_files:
        cmd.extend(["--context-file", path])
    return cmd


def build_loop_command(args: argparse.Namespace) -> list[str]:
    cmd = [
        "uv",
        "run",
        "python",
        "scripts/run_loop.py",
        "--enable-worker",
    ]
    if not args.initialize_on_start:
        cmd.append("--no-initialize-on-start")
    if not args.phase_logs:
        cmd.append("--no-phase-logs")
    if args.skip_loop_verify:
        cmd.append("--skip-verify")

    append_optional_flag(cmd, "--max-iterations", args.max_iterations)
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
    append_optional_flag(cmd, "--priority-refresh-theorem-interval", args.priority_refresh_theorem_interval)
    append_optional_flag(cmd, "--open-problem-prune-threshold", args.open_problem_prune_threshold)
    append_optional_flag(cmd, "--open-problem-failure-prune-threshold", args.open_problem_failure_prune_threshold)
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
    return cmd


def build_review_command(args: argparse.Namespace) -> list[str]:
    cmd = [
        "uv",
        "run",
        "python",
        "scripts/direct_refactor_derived.py",
        "--input-file",
        args.preview_file,
        "--output-file",
        args.review_output_file,
        "--sandbox",
        args.review_sandbox,
    ]
    append_optional_flag(cmd, "--model", args.review_model)
    if args.no_review_verify:
        cmd.append("--no-verify")
    return cmd


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate seeds from the active Theory.lean and context files, run the loop, "
            "then run both Derived refactor passes."
        )
    )
    parser.add_argument(
        "--article-file",
        dest="context_files",
        action="append",
        default=[],
        help="Extra article/context file to read during seed generation. Repeatable.",
    )
    parser.add_argument(
        "--context-file",
        dest="context_files",
        action="append",
        help="Alias of --article-file.",
    )
    parser.add_argument("--seed-count", type=int, default=4)
    parser.add_argument("--seed-src", default="seed")
    parser.add_argument("--seed-extra-instruction", default="")
    parser.add_argument("--seed-model")
    parser.add_argument("--seed-sandbox", default="read-only")
    parser.add_argument("--initialize-on-start", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--max-iterations", type=int)
    parser.add_argument("--phase-logs", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--skip-loop-verify", action="store_true")
    parser.add_argument("--worker-command")
    parser.add_argument("--worker-timeout", type=int)
    parser.add_argument("--prover-worker-command")
    parser.add_argument("--prover-worker-timeout", type=int)
    parser.add_argument("--prover-statement-worker-command")
    parser.add_argument("--prover-statement-worker-timeout", type=int)
    parser.add_argument("--formalize-worker-command")
    parser.add_argument("--formalize-worker-timeout", type=int)
    parser.add_argument("--repair-worker-command")
    parser.add_argument("--repair-worker-timeout", type=int)
    parser.add_argument("--prioritize-open-problems-worker-command")
    parser.add_argument("--prioritize-open-problems-worker-timeout", type=int)
    parser.add_argument("--priority-refresh-theorem-interval", type=int)
    parser.add_argument("--open-problem-prune-threshold", type=int)
    parser.add_argument("--open-problem-failure-prune-threshold", type=int)
    parser.add_argument("--refactor-worker-command")
    parser.add_argument("--refactor-worker-timeout", type=int)
    parser.add_argument("--refactor-verify-timeout", type=int)
    parser.add_argument("--preview-file", default=str(DEFAULT_PREVIEW))
    parser.add_argument("--review-output-file", default=str(DEFAULT_REVIEWED))
    parser.add_argument("--review-model")
    parser.add_argument("--review-sandbox", default="workspace-write")
    parser.add_argument("--no-review-verify", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()

    seed_cmd = build_seed_command(args)
    loop_cmd = build_loop_command(args)
    refactor_cmd = build_refactor_command(args)
    review_cmd = build_review_command(args)

    run_stage("seed-generation", seed_cmd, dry_run=args.dry_run)
    run_stage("main-loop", loop_cmd, dry_run=args.dry_run)
    run_stage("refactor-pass-1", refactor_cmd, dry_run=args.dry_run)
    run_stage("refactor-pass-2", review_cmd, dry_run=args.dry_run)

    if args.dry_run:
        print("[pipeline] dry-run only; no stage was executed.", file=sys.stderr, flush=True)
        return 0

    print(
        "Pipeline completed.\n"
        f"- theory: {DEFAULT_THEORY}\n"
        f"- seeds: {DEFAULT_SEEDS}\n"
        f"- derived: {DEFAULT_DERIVED}\n"
        f"- refactor preview: {args.preview_file}\n"
        f"- reviewed output: {args.review_output_file}",
        file=sys.stderr,
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
