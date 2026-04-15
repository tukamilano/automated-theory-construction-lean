from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime
from dataclasses import dataclass
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
SCRIPTS_ROOT = SCRIPT_DIR.parent
scripts_root_str = str(SCRIPTS_ROOT)
if scripts_root_str not in sys.path:
    sys.path.insert(0, scripts_root_str)

from atc_paths import loop_theory_state_path
from atc_paths import refactor_data_dir
from append_derived import promote_staging_to_product
from append_derived import reset_staging_derived_file
from theorem_store import ensure_product_file
from theorem_store import product_file_for_derived

REPO_ROOT = SCRIPTS_ROOT.parent

DEFAULT_PREVIEW_FILE = "AutomatedTheoryConstruction/Derived.refactored.preview.lean"
DEFAULT_ALPHA_DEDUPE_REPORT_FILE = "AutomatedTheoryConstruction/Derived.alpha_dedupe.report.json"
DEFAULT_REVIEW_OUTPUT_FILE = "AutomatedTheoryConstruction/Derived.refactored.reviewed.lean"
DEFAULT_REVIEW_REPORT_FILE = "AutomatedTheoryConstruction/Derived.refactored.reviewed.report.json"
DEFAULT_TRY_AT_EACH_STEP_RAW_OUTPUT_FILE = "AutomatedTheoryConstruction/Derived.tryAtEachStep.json"
DEFAULT_TRY_AT_EACH_STEP_APPLY_REPORT_FILE = "AutomatedTheoryConstruction/Derived.tryAtEachStep.apply_report.json"


@dataclass(frozen=True)
class RefactorPaths:
    artifact_dir: Path
    preview_file: Path
    alpha_dedupe_report_file: Path
    review_output_file: Path
    review_report_file: Path
    raw_output_file: Path
    apply_report_file: Path


@dataclass
class CycleStatus:
    loop_status: str
    paper_claim_status: str
    refactor_status: str
    fatal_stage: str
    paper_claim_report: dict[str, Any]
    current_iteration: int


def iso_timestamp_now() -> str:
    return datetime.now().astimezone().isoformat(timespec="seconds")


def _script_path(relative_path: str) -> str:
    return str((SCRIPTS_ROOT / relative_path).resolve())


def _append_flag(cmd: list[str], flag: str, value: str | int | Path | None) -> None:
    if value is None:
        return
    if isinstance(value, str) and not value:
        return
    cmd.extend([flag, str(value)])


def _append_bool_flag(cmd: list[str], flag: str, enabled: bool) -> None:
    cmd.append(flag if enabled else f"--no-{flag.removeprefix('--')}")


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    return json.loads(path.read_text(encoding="utf-8"))


def _read_current_iteration(data_dir: Path) -> int:
    payload = _load_json(loop_theory_state_path(data_dir))
    return int(payload.get("updated_at_iteration", 0) or 0)


def _next_cycle_snapshot_dir(snapshot_root: Path) -> tuple[str, Path]:
    snapshot_root.mkdir(parents=True, exist_ok=True)
    index = 1
    while True:
        cycle_id = f"cycle_{index:04d}"
        candidate = snapshot_root / cycle_id
        if not candidate.exists():
            return cycle_id, candidate
        index += 1


def _resolve_refactor_artifact_path(*, raw_path: str, default_path: str, artifact_dir: Path) -> Path:
    if raw_path == default_path:
        return artifact_dir / Path(default_path).name
    return Path(raw_path)


def _run_stage(name: str, cmd: list[str], *, env: dict[str, str]) -> int:
    print(f"[cycle] {name}: {' '.join(cmd)}", file=sys.stderr, flush=True)
    completed = subprocess.run(
        cmd,
        cwd=str(REPO_ROOT),
        env=env,
        check=False,
    )
    return completed.returncode


def _copy_into_snapshot(source: Path, snapshot_dir: Path) -> None:
    if not source.exists():
        return
    resolved_source = source.resolve()
    try:
        relative_source = resolved_source.relative_to(REPO_ROOT)
    except ValueError:
        relative_source = Path(source.name)
    destination = snapshot_dir / relative_source
    if source.is_dir():
        shutil.copytree(resolved_source, destination, dirs_exist_ok=True)
        return
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(resolved_source, destination)


def _write_cycle_manifest(snapshot_dir: Path, payload: dict[str, Any]) -> None:
    snapshot_dir.mkdir(parents=True, exist_ok=True)
    (snapshot_dir / "cycle_manifest.json").write_text(
        json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def _summarize_paper_claim_report(report: dict[str, Any]) -> dict[str, Any]:
    return {
        "status": str(report.get("status", "")),
        "processed": bool(report.get("processed", False)),
        "verify_success": bool(report.get("verify_success", False)),
        "candidate_id": str(report.get("candidate_id", "")),
        "theorem_name": str(report.get("theorem_name", "")),
        "stored_expand_row_count": len(report.get("stored_expand_rows", [])),
        "followup_candidate_count": len(report.get("followup_candidates", [])),
        "post_theorem_expand_candidate_count": len(report.get("post_theorem_expand_candidates", [])),
    }


def _resolve_refactor_paths(args: argparse.Namespace, *, data_dir: Path, cycle_id: str) -> RefactorPaths:
    artifact_dir = refactor_data_dir(data_dir) / cycle_id
    return RefactorPaths(
        artifact_dir=artifact_dir,
        preview_file=_resolve_refactor_artifact_path(
            raw_path=DEFAULT_PREVIEW_FILE,
            default_path=DEFAULT_PREVIEW_FILE,
            artifact_dir=artifact_dir,
        ),
        review_output_file=_resolve_refactor_artifact_path(
            raw_path=DEFAULT_REVIEW_OUTPUT_FILE,
            default_path=DEFAULT_REVIEW_OUTPUT_FILE,
            artifact_dir=artifact_dir,
        ),
        alpha_dedupe_report_file=_resolve_refactor_artifact_path(
            raw_path=DEFAULT_ALPHA_DEDUPE_REPORT_FILE,
            default_path=DEFAULT_ALPHA_DEDUPE_REPORT_FILE,
            artifact_dir=artifact_dir,
        ),
        review_report_file=_resolve_refactor_artifact_path(
            raw_path=DEFAULT_REVIEW_REPORT_FILE,
            default_path=DEFAULT_REVIEW_REPORT_FILE,
            artifact_dir=artifact_dir,
        ),
        raw_output_file=_resolve_refactor_artifact_path(
            raw_path=DEFAULT_TRY_AT_EACH_STEP_RAW_OUTPUT_FILE,
            default_path=DEFAULT_TRY_AT_EACH_STEP_RAW_OUTPUT_FILE,
            artifact_dir=artifact_dir,
        ),
        apply_report_file=_resolve_refactor_artifact_path(
            raw_path=DEFAULT_TRY_AT_EACH_STEP_APPLY_REPORT_FILE,
            default_path=DEFAULT_TRY_AT_EACH_STEP_APPLY_REPORT_FILE,
            artifact_dir=artifact_dir,
        ),
    )


def _run_loop_stage(
    *,
    args: argparse.Namespace,
    env: dict[str, str],
    start_iteration: int,
) -> int:
    loop_cmd = [sys.executable, _script_path("loop/run_loop.py")]
    _append_bool_flag(loop_cmd, "--initialize-on-start", bool(args.initialize_on_start))
    _append_bool_flag(loop_cmd, "--phase-logs", bool(args.phase_logs))
    if args.skip_verify:
        loop_cmd.append("--skip-verify")
    _append_flag(loop_cmd, "--worker-command", args.worker_command)
    _append_flag(loop_cmd, "--worker-timeout", args.worker_timeout)
    _append_flag(loop_cmd, "--iteration-offset", start_iteration)
    _append_flag(loop_cmd, "--max-iterations", args.cycle_iterations)
    _append_flag(loop_cmd, "--parallel-sessions", args.parallel_sessions)
    _append_flag(loop_cmd, "--seed-count", args.seed_count)
    _append_flag(loop_cmd, "--open-problem-failure-threshold", args.open_problem_failure_threshold)
    _append_flag(loop_cmd, "--prover-retry-budget-sec", args.prover_retry_budget_sec)
    _append_flag(loop_cmd, "--formalization-retry-budget-sec", args.formalization_retry_budget_sec)
    _append_flag(loop_cmd, "--max-same-error-streak", args.max_same_error_streak)
    return _run_stage("loop", loop_cmd, env=env)


def _run_paper_claim_stage(
    *,
    args: argparse.Namespace,
    env: dict[str, str],
    theory_file: Path,
    derived_file: Path,
    scratch_file: Path,
    data_dir: Path,
    cycle_id: str,
    current_iteration: int,
    phase_attempts_file: Path | None,
) -> tuple[str, dict[str, Any]]:
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as tmp:
        report_file = Path(tmp.name)
    try:
        paper_claim_cmd = [
            sys.executable,
            _script_path("paper_claim/run_paper_claim_session.py"),
            "--enable-worker",
            "--theory-file",
            str(theory_file),
            "--derived-file",
            str(derived_file),
            "--scratch-file",
            str(scratch_file),
            "--data-dir",
            str(data_dir),
            "--run-id",
            cycle_id,
            "--current-iteration",
            str(current_iteration),
            "--report-file",
            str(report_file),
            "--batch-generator-seed-count",
            str(args.seed_count),
            "--batch-generator-open-target-min",
            str(args.batch_generator_open_target_min),
            "--open-problem-failure-threshold",
            str(args.open_problem_failure_threshold),
            "--paper-claim-retry-budget-sec",
            str(args.formalization_retry_budget_sec),
        ]
        _append_flag(paper_claim_cmd, "--phase-attempts-file", phase_attempts_file)
        _append_flag(paper_claim_cmd, "--worker-command", args.worker_command)
        _append_flag(paper_claim_cmd, "--worker-timeout", args.worker_timeout)
        _append_bool_flag(paper_claim_cmd, "--phase-logs", bool(args.phase_logs))
        if args.skip_verify:
            paper_claim_cmd.append("--skip-verify")
        paper_claim_returncode = _run_stage("paper-claim", paper_claim_cmd, env=env)
        paper_claim_report = (
            json.loads(report_file.read_text(encoding="utf-8"))
            if report_file.exists()
            else {}
        )
        if paper_claim_returncode != 0 and not paper_claim_report:
            paper_claim_report = {
                "status": "paper_claim_error",
                "processed": False,
                "verify_success": False,
            }
        paper_claim_status = str(paper_claim_report.get("status", "ok" if paper_claim_returncode == 0 else "error"))
        return paper_claim_status, paper_claim_report
    finally:
        report_file.unlink(missing_ok=True)


def _run_refactor_stage(
    *,
    args: argparse.Namespace,
    env: dict[str, str],
    derived_file: Path,
    paths: RefactorPaths,
) -> str:
    product_file = product_file_for_derived(derived_file)
    ensure_product_file(product_file)
    paths.artifact_dir.mkdir(parents=True, exist_ok=True)
    print(f"[cycle] refactor-preview-copy: {derived_file} -> {paths.preview_file}", file=sys.stderr, flush=True)
    paths.preview_file.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(derived_file, paths.preview_file)

    alpha_dedupe_cmd = [
        sys.executable,
        _script_path("refactor/delete_alpha_equiv_duplicates.py"),
        "--input-file",
        str(paths.preview_file),
        "--output-file",
        str(paths.preview_file),
        "--alpha-source-file",
        str(derived_file),
        "--build-target",
        "AutomatedTheoryConstruction.Derived",
        "--equivalence-mode",
        "defeq",
        "--report-file",
        str(paths.alpha_dedupe_report_file),
    ]
    if _run_stage("alpha-dedupe-pre-pass-1_5", alpha_dedupe_cmd, env=env) != 0:
        return "alpha_dedupe_error"

    rewrite_cmd = [
        sys.executable,
        _script_path("refactor/apply_try_at_each_step_rewrites.py"),
        "--input-file",
        str(paths.preview_file),
        "--output-file",
        str(paths.preview_file),
        "--raw-output-file",
        str(paths.raw_output_file),
        "--apply-report-file",
        str(paths.apply_report_file),
        "--tactic",
        "with_reducible exact?",
    ]
    if _run_stage("rewrite", rewrite_cmd, env=env) != 0:
        return "rewrite_error"

    review_cmd = [
        sys.executable,
        _script_path("refactor/direct_refactor_derived.py"),
        "--input-file",
        str(paths.preview_file),
        "--output-file",
        str(paths.review_output_file),
        "--report-file",
        str(paths.review_report_file),
    ]
    if _run_stage("review", review_cmd, env=env) != 0:
        return "review_error"

    original_product = product_file.read_text(encoding="utf-8") if product_file.exists() else ""
    original_derived = derived_file.read_text(encoding="utf-8") if derived_file.exists() else ""
    print(f"[cycle] refactor-promote-review: {paths.review_output_file} -> {product_file}", file=sys.stderr, flush=True)
    try:
        promote_staging_to_product(product_file, paths.review_output_file)
        reset_staging_derived_file(derived_file)
        product_build = _run_stage("product-build", ["lake", "build", "AutomatedTheoryConstruction.Product"], env=env)
        if product_build != 0:
            raise RuntimeError("product build failed")
        derived_build = _run_stage("derived-build", ["lake", "build", "AutomatedTheoryConstruction.Derived"], env=env)
        if derived_build != 0:
            raise RuntimeError("derived build failed")
    except Exception:
        product_file.write_text(original_product, encoding="utf-8")
        derived_file.write_text(original_derived, encoding="utf-8")
        return "promote_error"
    return "ok"


def _write_cycle_snapshot(
    *,
    snapshot_dir: Path,
    theory_file: Path,
    derived_file: Path,
    data_dir: Path,
    cycle_id: str,
    started_at: str,
    start_iteration: int,
    target_iteration: int,
    status: CycleStatus,
    paths: RefactorPaths,
) -> None:
    product_file = product_file_for_derived(derived_file)
    finished_at = iso_timestamp_now()
    overall_status = "ok" if not status.fatal_stage else "error"
    snapshot_paths = [
        theory_file,
        product_file,
        derived_file,
        data_dir,
    ]
    for config_name in (
        "configs/atc.json",
        "configs/atc.toml",
        "atc.json",
        "atc.toml",
    ):
        config_path = REPO_ROOT / config_name
        if config_path.exists():
            snapshot_paths.append(config_path)
    for path in snapshot_paths:
        _copy_into_snapshot(path, snapshot_dir)
    _write_cycle_manifest(
        snapshot_dir,
        {
            "cycle_id": cycle_id,
            "status": overall_status,
            "fatal_stage": status.fatal_stage,
            "started_at": started_at,
            "finished_at": finished_at,
            "start_iteration": start_iteration,
            "target_iteration": target_iteration,
            "end_iteration": status.current_iteration,
            "loop_status": status.loop_status,
            "paper_claim_status": status.paper_claim_status,
            "refactor_status": status.refactor_status,
            "paper_claim_report": _summarize_paper_claim_report(status.paper_claim_report),
            "paths": {
                "theory_file": str(theory_file),
                "product_file": str(product_file),
                "derived_file": str(derived_file),
                "data_dir": str(data_dir),
                "refactor_artifact_dir": str(paths.artifact_dir),
                "preview_file": str(paths.preview_file),
                "alpha_dedupe_report_file": str(paths.alpha_dedupe_report_file),
                "review_output_file": str(paths.review_output_file),
                "review_report_file": str(paths.review_report_file),
                "try_at_each_step_raw_output_file": str(paths.raw_output_file),
                "try_at_each_step_apply_report_file": str(paths.apply_report_file),
            },
        },
    )


def main() -> int:
    parser = argparse.ArgumentParser(description="Run one ATC cycle: loop -> paper claim -> refactor -> snapshot.")
    parser.add_argument("--theory-file", default="AutomatedTheoryConstruction/Theory.lean")
    parser.add_argument("--derived-file", default="AutomatedTheoryConstruction/Derived.lean")
    parser.add_argument("--scratch-file", default="AutomatedTheoryConstruction/Scratch.lean")
    parser.add_argument("--worker-command")
    parser.add_argument("--worker-timeout", type=int)
    parser.add_argument("--data-dir", default="data")
    parser.add_argument("--phase-attempts-file")
    parser.add_argument("--snapshot-root", default="snapshots")
    parser.add_argument("--cycle-iterations", type=int, default=20)
    parser.add_argument("--parallel-sessions", type=int, default=1)
    parser.add_argument("--seed-count", type=int, default=4)
    parser.add_argument("--batch-generator-open-target-min", type=int, default=2)
    parser.add_argument("--open-problem-failure-threshold", type=int, default=2)
    parser.add_argument("--prover-retry-budget-sec", type=int, default=120)
    parser.add_argument("--formalization-retry-budget-sec", type=int, default=300)
    parser.add_argument("--max-same-error-streak", type=int, default=5)
    parser.add_argument("--initialize-on-start", action=argparse.BooleanOptionalAction, default=False)
    parser.add_argument("--phase-logs", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--skip-verify", action="store_true")
    args = parser.parse_args()

    theory_file = Path(args.theory_file)
    derived_file = Path(args.derived_file)
    scratch_file = Path(args.scratch_file)
    data_dir = Path(args.data_dir)
    snapshot_root = Path(args.snapshot_root)
    phase_attempts_file = Path(args.phase_attempts_file) if args.phase_attempts_file else None

    start_iteration = _read_current_iteration(data_dir)
    target_iteration = start_iteration + args.cycle_iterations
    cycle_id, snapshot_dir = _next_cycle_snapshot_dir(snapshot_root)
    refactor_paths = _resolve_refactor_paths(args, data_dir=data_dir, cycle_id=cycle_id)
    started_at = iso_timestamp_now()
    env = os.environ.copy()
    status = CycleStatus(
        loop_status="pending",
        paper_claim_status="pending",
        refactor_status="pending",
        fatal_stage="",
        paper_claim_report={},
        current_iteration=start_iteration,
    )

    try:
        loop_returncode = _run_loop_stage(
            args=args,
            env=env,
            start_iteration=start_iteration,
        )
        status.current_iteration = _read_current_iteration(data_dir)
        status.loop_status = "ok" if loop_returncode == 0 else "error"
        if loop_returncode != 0:
            status.fatal_stage = "loop"
            return 1

        status.paper_claim_status, status.paper_claim_report = _run_paper_claim_stage(
            args=args,
            env=env,
            theory_file=theory_file,
            derived_file=derived_file,
            scratch_file=scratch_file,
            data_dir=data_dir,
            cycle_id=cycle_id,
            current_iteration=status.current_iteration,
            phase_attempts_file=phase_attempts_file,
        )

        status.refactor_status = _run_refactor_stage(
            args=args,
            env=env,
            derived_file=derived_file,
            paths=refactor_paths,
        )
        if status.refactor_status != "ok":
            status.fatal_stage = "refactor"
            return 1

        return 0
    finally:
        status.current_iteration = _read_current_iteration(data_dir)
        _write_cycle_snapshot(
            snapshot_dir=snapshot_dir,
            theory_file=theory_file,
            derived_file=derived_file,
            data_dir=data_dir,
            cycle_id=cycle_id,
            started_at=started_at,
            start_iteration=start_iteration,
            target_iteration=target_iteration,
            status=status,
            paths=refactor_paths,
        )


if __name__ == "__main__":
    raise SystemExit(main())
