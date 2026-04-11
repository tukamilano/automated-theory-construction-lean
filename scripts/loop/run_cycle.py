from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
SCRIPTS_ROOT = SCRIPT_DIR.parent
REPO_ROOT = SCRIPTS_ROOT.parent

DEFAULT_PREVIEW_FILE = "AutomatedTheoryConstruction/Derived.refactored.preview.lean"
DEFAULT_REVIEW_OUTPUT_FILE = "AutomatedTheoryConstruction/Derived.refactored.reviewed.lean"
DEFAULT_REVIEW_REPORT_FILE = "AutomatedTheoryConstruction/Derived.refactored.reviewed.report.json"
DEFAULT_TRY_AT_EACH_STEP_RAW_OUTPUT_FILE = "AutomatedTheoryConstruction/Derived.tryAtEachStep.json"
DEFAULT_TRY_AT_EACH_STEP_APPLY_REPORT_FILE = "AutomatedTheoryConstruction/Derived.tryAtEachStep.apply_report.json"
DEFAULT_PLAN_FILE = "data/derived-chunk-plan.json"


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
    payload = _load_json(data_dir / "theory_state.json")
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


def _summarize_main_theorem_report(report: dict[str, Any]) -> dict[str, Any]:
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


def main() -> int:
    parser = argparse.ArgumentParser(description="Run one ATC cycle: loop -> main theorem -> refactor -> snapshot.")
    parser.add_argument("--theory-file", default="AutomatedTheoryConstruction/Theory.lean")
    parser.add_argument("--derived-file", default="AutomatedTheoryConstruction/Derived.lean")
    parser.add_argument("--scratch-file", default="AutomatedTheoryConstruction/Scratch.lean")
    parser.add_argument("--worker-command")
    parser.add_argument("--worker-timeout", type=int)
    parser.add_argument("--data-dir", default="data")
    parser.add_argument("--formalization-memory-file", default="data/formalization_memory.json")
    parser.add_argument("--phase-attempts-file")
    parser.add_argument("--preview-file", default=DEFAULT_PREVIEW_FILE)
    parser.add_argument("--review-output-file", default=DEFAULT_REVIEW_OUTPUT_FILE)
    parser.add_argument("--review-report-file", default=DEFAULT_REVIEW_REPORT_FILE)
    parser.add_argument("--try-at-each-step-raw-output-file", default=DEFAULT_TRY_AT_EACH_STEP_RAW_OUTPUT_FILE)
    parser.add_argument("--try-at-each-step-apply-report-file", default=DEFAULT_TRY_AT_EACH_STEP_APPLY_REPORT_FILE)
    parser.add_argument("--try-at-each-step-tactic", default="with_reducible exact?")
    parser.add_argument("--theorem-reuse-memory-file", default="data/theorem_reuse_memory.json")
    parser.add_argument("--deps-file", default="data/derived-deps.json")
    parser.add_argument("--generated-root", default="AutomatedTheoryConstruction/Generated")
    parser.add_argument("--manifest-file", default="AutomatedTheoryConstruction/Generated/Manifest.lean")
    parser.add_argument("--catalog-file", default="AutomatedTheoryConstruction/Generated/catalog.json")
    parser.add_argument("--plan-file", default=DEFAULT_PLAN_FILE)
    parser.add_argument("--refactor-artifact-dir")
    parser.add_argument("--snapshot-root", default="snapshots")
    parser.add_argument("--cycle-iterations", type=int, default=20)
    parser.add_argument("--parallel-sessions", type=int, default=1)
    parser.add_argument("--seed-count", type=int, default=4)
    parser.add_argument("--batch-generator-open-target-min", type=int, default=2)
    parser.add_argument("--open-problem-failure-threshold", type=int, default=2)
    parser.add_argument("--prover-retry-budget-sec", type=int, default=120)
    parser.add_argument("--formalization-retry-budget-sec", type=int, default=300)
    parser.add_argument("--max-same-error-streak", type=int, default=5)
    parser.add_argument("--generated-repair-verify-timeout", type=int, default=300)
    parser.add_argument("--generated-local-worker-timeout", type=int, default=390)
    parser.add_argument("--generated-local-manifest-verify-timeout", type=int, default=300)
    parser.add_argument("--generated-local-max-rounds-per-pass", type=int, default=5)
    parser.add_argument("--initialize-on-start", action=argparse.BooleanOptionalAction, default=False)
    parser.add_argument("--phase-logs", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--skip-verify", action="store_true")
    parser.add_argument("--skip-main-theorem", action="store_true")
    parser.add_argument("--skip-refactor", action="store_true")
    args = parser.parse_args()

    theory_file = Path(args.theory_file)
    derived_file = Path(args.derived_file)
    scratch_file = Path(args.scratch_file)
    data_dir = Path(args.data_dir)
    theorem_reuse_memory_file = Path(args.theorem_reuse_memory_file)
    deps_file = Path(args.deps_file)
    generated_root = Path(args.generated_root)
    manifest_file = Path(args.manifest_file)
    catalog_file = Path(args.catalog_file)
    snapshot_root = Path(args.snapshot_root)
    phase_attempts_file = Path(args.phase_attempts_file) if args.phase_attempts_file else None

    start_iteration = _read_current_iteration(data_dir)
    target_iteration = start_iteration + args.cycle_iterations
    cycle_id, snapshot_dir = _next_cycle_snapshot_dir(snapshot_root)
    refactor_artifact_dir = (
        Path(args.refactor_artifact_dir)
        if args.refactor_artifact_dir
        else data_dir / "runs" / cycle_id / "refactor"
    )
    preview_file = _resolve_refactor_artifact_path(
        raw_path=args.preview_file,
        default_path=DEFAULT_PREVIEW_FILE,
        artifact_dir=refactor_artifact_dir,
    )
    review_output_file = _resolve_refactor_artifact_path(
        raw_path=args.review_output_file,
        default_path=DEFAULT_REVIEW_OUTPUT_FILE,
        artifact_dir=refactor_artifact_dir,
    )
    review_report_file = _resolve_refactor_artifact_path(
        raw_path=args.review_report_file,
        default_path=DEFAULT_REVIEW_REPORT_FILE,
        artifact_dir=refactor_artifact_dir,
    )
    raw_output_file = _resolve_refactor_artifact_path(
        raw_path=args.try_at_each_step_raw_output_file,
        default_path=DEFAULT_TRY_AT_EACH_STEP_RAW_OUTPUT_FILE,
        artifact_dir=refactor_artifact_dir,
    )
    apply_report_file = _resolve_refactor_artifact_path(
        raw_path=args.try_at_each_step_apply_report_file,
        default_path=DEFAULT_TRY_AT_EACH_STEP_APPLY_REPORT_FILE,
        artifact_dir=refactor_artifact_dir,
    )
    plan_file = _resolve_refactor_artifact_path(
        raw_path=args.plan_file,
        default_path=DEFAULT_PLAN_FILE,
        artifact_dir=refactor_artifact_dir,
    )
    started_at = iso_timestamp_now()
    env = os.environ.copy()
    loop_status = "pending"
    main_theorem_status = "skipped" if args.skip_main_theorem else "pending"
    refactor_status = "skipped" if args.skip_refactor else "pending"
    fatal_stage = ""
    main_theorem_report: dict[str, Any] = {}
    current_iteration = start_iteration

    try:
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
        loop_returncode = _run_stage("loop", loop_cmd, env=env)
        current_iteration = _read_current_iteration(data_dir)
        loop_status = "ok" if loop_returncode == 0 else "error"
        if loop_returncode != 0:
            fatal_stage = "loop"
            return 1

        if not args.skip_main_theorem:
            with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as tmp:
                report_file = Path(tmp.name)
            try:
                main_theorem_cmd = [
                    sys.executable,
                    _script_path("main_theorem/run_main_theorem_session.py"),
                    "--enable-worker",
                    "--theory-file",
                    str(theory_file),
                    "--derived-file",
                    str(derived_file),
                    "--scratch-file",
                    str(scratch_file),
                    "--data-dir",
                    str(data_dir),
                    "--formalization-memory-file",
                    str(args.formalization_memory_file),
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
                    "--formalization-retry-budget-sec",
                    str(args.formalization_retry_budget_sec),
                    "--max-same-error-streak",
                    str(args.max_same_error_streak),
                ]
                _append_flag(main_theorem_cmd, "--phase-attempts-file", phase_attempts_file)
                _append_flag(main_theorem_cmd, "--worker-command", args.worker_command)
                _append_flag(main_theorem_cmd, "--worker-timeout", args.worker_timeout)
                _append_bool_flag(main_theorem_cmd, "--phase-logs", bool(args.phase_logs))
                if args.skip_verify:
                    main_theorem_cmd.append("--skip-verify")
                main_theorem_returncode = _run_stage("main-theorem", main_theorem_cmd, env=env)
                if report_file.exists():
                    main_theorem_report = json.loads(report_file.read_text(encoding="utf-8"))
                if main_theorem_returncode != 0 and not main_theorem_report:
                    main_theorem_report = {
                        "status": "main_theorem_error",
                        "processed": False,
                        "verify_success": False,
                    }
                main_theorem_status = str(main_theorem_report.get("status", "ok" if main_theorem_returncode == 0 else "error"))
            finally:
                report_file.unlink(missing_ok=True)

        if not args.skip_refactor:
            refactor_artifact_dir.mkdir(parents=True, exist_ok=True)
            print(f"[cycle] refactor-preview-copy: {derived_file} -> {preview_file}", file=sys.stderr, flush=True)
            preview_file.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(derived_file, preview_file)

            rewrite_cmd = [
                sys.executable,
                _script_path("refactor/apply_try_at_each_step_rewrites.py"),
                "--input-file",
                str(preview_file),
                "--output-file",
                str(preview_file),
                "--raw-output-file",
                str(raw_output_file),
                "--apply-report-file",
                str(apply_report_file),
                "--tactic",
                args.try_at_each_step_tactic,
            ]
            if _run_stage("rewrite", rewrite_cmd, env=env) != 0:
                refactor_status = "rewrite_error"
                fatal_stage = "refactor"
                return 1

            review_cmd = [
                sys.executable,
                _script_path("refactor/direct_refactor_derived.py"),
                "--input-file",
                str(preview_file),
                "--output-file",
                str(review_output_file),
                "--report-file",
                str(review_report_file),
            ]
            if _run_stage("review", review_cmd, env=env) != 0:
                refactor_status = "review_error"
                fatal_stage = "refactor"
                return 1

            print(f"[cycle] refactor-promote-review: {review_output_file} -> {derived_file}", file=sys.stderr, flush=True)
            shutil.copyfile(review_output_file, derived_file)

            materialize_cmd = [
                sys.executable,
                _script_path("refactor/refactor_derived_to_generated.py"),
                "--derived-file",
                str(derived_file),
                "--deps-file",
                str(deps_file),
                "--theory-file",
                str(theory_file),
                "--theorem-reuse-memory-file",
                str(theorem_reuse_memory_file),
                "--generated-root",
                str(generated_root),
                "--manifest-file",
                str(manifest_file),
                "--catalog-file",
                str(catalog_file),
                "--plan-file",
                str(plan_file),
                "--generated-repair-verify-timeout",
                str(args.generated_repair_verify_timeout),
            ]
            if _run_stage("materialize-generated", materialize_cmd, env=env) != 0:
                refactor_status = "materialize_error"
                fatal_stage = "refactor"
                return 1

            local_pass_cmd = [
                sys.executable,
                _script_path("refactor/run_generated_local_passes.py"),
                "--generated-root",
                str(generated_root),
                "--theory-file",
                str(theory_file),
                "--theorem-reuse-memory-file",
                str(theorem_reuse_memory_file),
                "--worker-command",
                str(args.worker_command or ""),
                "--worker-timeout",
                str(args.generated_local_worker_timeout),
                "--manifest-verify-timeout",
                str(args.generated_local_manifest_verify_timeout),
                "--max-rounds-per-pass",
                str(args.generated_local_max_rounds_per_pass),
            ]
            if not args.worker_command:
                local_pass_cmd = [item for item in local_pass_cmd if item not in {"--worker-command", ""}]
            if _run_stage("generated-local-passes", local_pass_cmd, env=env) != 0:
                refactor_status = "local_pass_error"
                fatal_stage = "refactor"
                return 1
            refactor_status = "ok"

        return 0
    finally:
        finished_at = iso_timestamp_now()
        current_iteration = _read_current_iteration(data_dir)
        overall_status = "ok" if not fatal_stage else "error"
        snapshot_paths = [
            theory_file,
            derived_file,
            generated_root,
            data_dir,
        ]
        for config_name in ("atc.json", "atc.toml"):
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
                "fatal_stage": fatal_stage,
                "started_at": started_at,
                "finished_at": finished_at,
                "start_iteration": start_iteration,
                "target_iteration": target_iteration,
                "end_iteration": current_iteration,
                "loop_status": loop_status,
                "main_theorem_status": main_theorem_status,
                "refactor_status": refactor_status,
                "main_theorem_report": _summarize_main_theorem_report(main_theorem_report),
                "paths": {
                    "theory_file": str(theory_file),
                    "derived_file": str(derived_file),
                    "generated_root": str(generated_root),
                    "data_dir": str(data_dir),
                    "refactor_artifact_dir": str(refactor_artifact_dir),
                    "preview_file": str(preview_file),
                    "review_output_file": str(review_output_file),
                    "review_report_file": str(review_report_file),
                    "try_at_each_step_raw_output_file": str(raw_output_file),
                    "try_at_each_step_apply_report_file": str(apply_report_file),
                    "plan_file": str(plan_file),
                },
            },
        )


if __name__ == "__main__":
    raise SystemExit(main())
