from __future__ import annotations

import argparse
import json
import shlex
import subprocess
import sys
from pathlib import Path

from common import write_json_atomic


REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_THEORY = Path("AutomatedTheoryConstruction/Theory.lean")
DEFAULT_DERIVED = Path("AutomatedTheoryConstruction/Derived.lean")
DEFAULT_SEEDS = Path("AutomatedTheoryConstruction/seeds.jsonl")
DEFAULT_PREVIEW = Path("AutomatedTheoryConstruction/Derived.refactored.preview.lean")
DEFAULT_REVIEWED = Path("AutomatedTheoryConstruction/Derived.refactored.reviewed.lean")
DATA_RUNS_DIR = REPO_ROOT / "data" / "runs"


def append_optional_flag(cmd: list[str], flag: str, value: str | int | None) -> None:
    if value is None:
        return
    text = str(value).strip()
    if not text:
        return
    cmd.extend([flag, text])


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


def list_loop_run_ids() -> set[str]:
    if not DATA_RUNS_DIR.exists():
        return set()
    return {
        path.name
        for path in DATA_RUNS_DIR.iterdir()
        if path.is_dir() and path.name.endswith("-loop")
    }


def newest_loop_summary_path() -> Path | None:
    if not DATA_RUNS_DIR.exists():
        return None
    loop_dirs = [
        path
        for path in DATA_RUNS_DIR.iterdir()
        if path.is_dir() and path.name.endswith("-loop")
    ]
    if not loop_dirs:
        return None
    latest_dir = max(loop_dirs, key=lambda path: path.stat().st_mtime_ns)
    return latest_dir / "summary.json"


def resolve_loop_summary_path(previous_run_ids: set[str]) -> Path | None:
    new_run_ids = list_loop_run_ids() - previous_run_ids
    if len(new_run_ids) == 1:
        run_id = next(iter(new_run_ids))
        return DATA_RUNS_DIR / run_id / "summary.json"
    return newest_loop_summary_path()


def parse_stage_json_report(stdout: str) -> dict[str, object] | None:
    for line in reversed(stdout.splitlines()):
        text = line.strip()
        if not text:
            continue
        try:
            payload = json.loads(text)
        except json.JSONDecodeError:
            continue
        if isinstance(payload, dict):
            return payload
    return None


def augment_run_summary_with_refactor(
    summary_path: Path,
    refactor_report: dict[str, object],
) -> None:
    if not summary_path.exists():
        return

    payload = json.loads(summary_path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        return

    input_count_raw = refactor_report.get("refactor_input_theorem_count")
    output_count_raw = refactor_report.get("refactor_output_theorem_count")
    removed_count: int | None = None
    if isinstance(input_count_raw, int) and isinstance(output_count_raw, int):
        removed_count = input_count_raw - output_count_raw

    payload["refactor_preview_status"] = str(refactor_report.get("status", "")).strip()
    payload["refactor_preview_verify_success"] = bool(refactor_report.get("verify_success", False))
    payload["refactor_input_theorem_count"] = input_count_raw
    payload["refactor_output_theorem_count"] = output_count_raw
    payload["refactor_removed_theorem_count"] = removed_count
    payload["stage1_refactor_compression_rate"] = refactor_report.get("stage1_refactor_compression_rate")
    payload["refactor_preview_output_file"] = refactor_report.get("output_file")

    write_json_atomic(summary_path, payload)


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
        "--enable-worker",
        "--no-initialize-on-start",
    ]
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
    append_optional_flag(cmd, "--open-problem-failure-threshold", args.open_problem_failure_threshold)
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
            "Generate seeds from the active Theory.lean entry module, its local imports, and context files, run the loop, "
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
    parser.add_argument("--open-problem-failure-threshold", type=int)
    parser.add_argument("--main-theorem-interval", type=int)
    parser.add_argument("--main-theorem-formalize-worker-timeout", type=int)
    parser.add_argument("--main-theorem-repair-worker-timeout", type=int)
    parser.add_argument("--main-theorem-verify-timeout", type=int)
    parser.add_argument("--main-theorem-formalization-retry-budget-sec", type=int)
    parser.add_argument("--refactor-worker-command")
    parser.add_argument("--refactor-worker-timeout", type=int)
    parser.add_argument("--refactor-verify-timeout", type=int)
    parser.add_argument("--preview-file", default=str(DEFAULT_PREVIEW))
    parser.add_argument("--review-output-file", default=str(DEFAULT_REVIEWED))
    parser.add_argument("--review-model")
    parser.add_argument("--review-sandbox", default="workspace-write")
    parser.add_argument("--no-review-verify", action="store_true")
    parser.add_argument("--run-seed", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--run-refactor-pass-1", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--run-refactor-pass-2", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--run-main-theorem-session", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--dry-run", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()

    seed_cmd = build_seed_command(args)
    loop_cmd = build_loop_command(args)
    refactor_cmd = build_refactor_command(args)
    review_input = args.preview_file
    loop_run_ids_before = list_loop_run_ids()

    if args.run_seed:
        require_success("seed-generation", run_stage("seed-generation", seed_cmd, dry_run=args.dry_run))
    else:
        print("[pipeline] seed-generation: skipped (--no-run-seed)", file=sys.stderr, flush=True)

    require_success("main-loop", run_stage("main-loop", loop_cmd, dry_run=args.dry_run))
    loop_summary_path = None if args.dry_run else resolve_loop_summary_path(loop_run_ids_before)

    if args.run_refactor_pass_1:
        refactor_result = run_stage("refactor-pass-1", refactor_cmd, dry_run=args.dry_run, capture_output=True)
        if stage_timed_out(refactor_result):
            print(
                "[pipeline] refactor-pass-1 timed out; falling back to direct review from Derived.lean",
                file=sys.stderr,
                flush=True,
            )
            review_input = str(DEFAULT_DERIVED)
        else:
            if (
                not args.dry_run
                and loop_summary_path is not None
                and refactor_result is not None
                and refactor_result.stdout
            ):
                refactor_report = parse_stage_json_report(refactor_result.stdout)
                if refactor_report is not None:
                    try:
                        augment_run_summary_with_refactor(loop_summary_path, refactor_report)
                    except Exception as exc:
                        print(
                            f"[pipeline] warning: failed to update {loop_summary_path} with refactor metrics: {exc}",
                            file=sys.stderr,
                            flush=True,
                        )
            require_success("refactor-pass-1", refactor_result)
    else:
        print("[pipeline] refactor-pass-1: skipped (--no-run-refactor-pass-1)", file=sys.stderr, flush=True)
        review_input = str(DEFAULT_DERIVED)

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
        f"- reviewed output: {args.review_output_file}",
        file=sys.stderr,
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
