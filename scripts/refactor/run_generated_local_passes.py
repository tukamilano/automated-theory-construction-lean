from __future__ import annotations

import argparse
import json
import math
import subprocess
import sys
import threading
import time
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
SCRIPTS_ROOT = SCRIPT_DIR.parent
scripts_root_str = str(SCRIPTS_ROOT)
if scripts_root_str not in sys.path:
    sys.path.insert(0, scripts_root_str)

from atc_paths import loop_theorem_reuse_memory_path
from append_derived import build_derived_entries_from_file
from common import load_theory_context
from derived_refactor_utils import build_report
from derived_refactor_utils import compare_theorem_inventories
from derived_refactor_utils import debug_log
from derived_refactor_utils import extract_theorem_entries_from_code
from derived_refactor_utils import load_prompt_text
from derived_refactor_utils import load_text
from derived_refactor_utils import print_report
from derived_refactor_utils import resolve_refactor_worker_settings
from derived_refactor_utils import validate_full_file_refactor_output
from generated_library import DEFAULT_GENERATED_ROOT
from generated_library import iter_generated_chunk_files
from plan_derived_compression import build_payload
from plan_derived_compression import validate_plan_output
from theorem_reuse_memory import load_theorem_reuse_memory
from theorem_reuse_memory import summarize_supporting_theorem_frequency
from worker_client import WorkerSettings
from worker_client import invoke_worker_json


REPO_ROOT = SCRIPTS_ROOT.parent
DEFAULT_THEORY = Path("AutomatedTheoryConstruction/Theory.lean")
DEFAULT_THEOREM_REUSE_MEMORY = loop_theorem_reuse_memory_path(Path("data"))
DEFAULT_EXECUTOR_PROMPT = Path("prompts/derived/compression_executor.md")

PASS_SPECS = (
    {
        "pass_name": "pass1.2",
        "prompt_file": Path("prompts/derived/compression_planner.md"),
        "allowed_kinds": {"exact_duplicate_collapse"},
    },
    {
        "pass_name": "pass1.3",
        "prompt_file": Path("prompts/derived/proof_retarget_planner.md"),
        "allowed_kinds": {"proof_retarget"},
    },
)

HEARTBEAT_INTERVAL_SEC = 30.0


def _timeout_label(timeout_sec: int | None) -> str:
    if timeout_sec in (None, 0):
        return "none"
    return f"{timeout_sec}s"


def _run_with_heartbeat(
    *,
    label: str,
    timeout_sec: int | None,
    fn: Any,
) -> Any:
    done = threading.Event()
    state: dict[str, Any] = {}
    started = time.monotonic()

    def _target() -> None:
        try:
            state["result"] = fn()
        except Exception as exc:  # pragma: no cover - passthrough wrapper
            state["exception"] = exc
        finally:
            done.set()

    debug_log(
        f"[generated-local] {label} start timeout={_timeout_label(timeout_sec)}"
    )
    worker = threading.Thread(target=_target, name="generated-local-heartbeat", daemon=True)
    worker.start()
    while not done.wait(HEARTBEAT_INTERVAL_SEC):
        elapsed = time.monotonic() - started
        debug_log(
            f"[generated-local] {label} heartbeat elapsed={elapsed:.1f}s timeout={_timeout_label(timeout_sec)}"
        )
    worker.join(timeout=1.0)
    elapsed = time.monotonic() - started
    if "exception" in state:
        debug_log(f"[generated-local] {label} error elapsed={elapsed:.1f}s")
        raise state["exception"]
    debug_log(f"[generated-local] {label} done elapsed={elapsed:.1f}s")
    return state.get("result")


def _single_line_excerpt(text: str, limit: int = 240) -> str:
    normalized = " ".join(text.strip().split())
    if not normalized:
        return ""
    if len(normalized) <= limit:
        return normalized
    return normalized[: limit - 3] + "..."


def _is_worker_timeout_error(exc: Exception) -> bool:
    message = str(exc).lower()
    if "keyboardinterrupt" in message or "exited with code 130" in message or "interrupt_requested" in message:
        return False
    return "timed out" in message or "timeout" in message


def _worker_failure_summary(*, phase: str, exc: Exception) -> str:
    return f"{phase} timeout" if _is_worker_timeout_error(exc) else f"{phase} worker error"


def _remaining_timeout_sec(deadline_monotonic: float | None) -> int | None:
    if deadline_monotonic is None:
        return None
    remaining = deadline_monotonic - time.monotonic()
    if remaining <= 0:
        return 0
    return max(1, math.ceil(remaining))


def _scoped_worker_settings(settings: WorkerSettings, timeout_sec: int | None) -> WorkerSettings:
    return WorkerSettings(
        command=settings.command,
        timeout_sec=timeout_sec,
        propagate_timeout=settings.propagate_timeout,
        codex_timeout_sec=settings.codex_timeout_sec,
        propagate_codex_timeout=settings.propagate_codex_timeout,
    )


def _run_manifest_build(timeout_sec: int | None) -> dict[str, Any]:
    try:
        completed = subprocess.run(
            ["lake", "build", "AutomatedTheoryConstruction.Generated.Manifest"],
            cwd=str(REPO_ROOT),
            check=False,
            capture_output=True,
            text=True,
            timeout=None if timeout_sec in (None, 0) else timeout_sec,
        )
    except subprocess.TimeoutExpired as exc:
        stdout_text = exc.stdout if isinstance(exc.stdout, str) else ""
        stderr_text = exc.stderr if isinstance(exc.stderr, str) else ""
        detail = "\n".join(part for part in (stdout_text, stderr_text) if part).strip()
        return {
            "success": False,
            "detail": f"manifest build timed out after {timeout_sec}s\n{detail}".strip(),
        }
    detail = "\n".join(part for part in (completed.stdout, completed.stderr) if part).strip()
    return {
        "success": completed.returncode == 0,
        "detail": detail,
    }


def _build_planner_payload(
    *,
    chunk_file: Path,
    theory_file: Path,
    theorem_reuse_memory_file: Path,
) -> dict[str, Any]:
    derived_code = load_text(chunk_file)
    _, theory_context = load_theory_context(theory_file, repo_root=REPO_ROOT)
    theorem_inventory = build_derived_entries_from_file(chunk_file)
    theorem_reuse_memory = load_theorem_reuse_memory(theorem_reuse_memory_file)
    supporting_theorem_frequency = summarize_supporting_theorem_frequency(theorem_reuse_memory)
    return build_payload(
        input_file=chunk_file,
        theory_file=theory_file,
        derived_code=derived_code,
        theory_context=theory_context,
        theorem_inventory=theorem_inventory,
        theorem_reuse_memory=theorem_reuse_memory,
        supporting_theorem_frequency=supporting_theorem_frequency,
    )


def _plan_items(
    *,
    chunk_file: Path,
    theory_file: Path,
    theorem_reuse_memory_file: Path,
    worker_settings: WorkerSettings,
    prompt_file: Path,
    allowed_kinds: set[str],
    pass_name: str,
    pass_deadline_monotonic: float | None,
) -> tuple[str, str, list[dict[str, Any]]]:
    prompt_text = load_prompt_text(prompt_file)
    payload = _build_planner_payload(
        chunk_file=chunk_file,
        theory_file=theory_file,
        theorem_reuse_memory_file=theorem_reuse_memory_file,
    )
    remaining_timeout_sec = _remaining_timeout_sec(pass_deadline_monotonic)
    if remaining_timeout_sec == 0:
        detail = f"pass budget exhausted before planning started for {chunk_file.name} {pass_name}"
        debug_log(f"[generated-local] {detail}")
        return "stuck", "planner budget exhausted", []
    try:
        raw_result, _worker_meta = _run_with_heartbeat(
            label=(
                f"plan chunk={chunk_file.name} pass={pass_name}"
            ),
            timeout_sec=remaining_timeout_sec,
            fn=lambda: invoke_worker_json(
                settings=_scoped_worker_settings(worker_settings, remaining_timeout_sec),
                task_type="plan_derived_compression",
                system_prompt=prompt_text,
                payload=payload,
                metadata={"input_file": str(chunk_file), "pass_name": pass_name},
            ),
        )
    except Exception as exc:
        detail = _single_line_excerpt(str(exc))
        debug_log(
            f"[generated-local] plan chunk={chunk_file.name} pass={pass_name} failed detail={detail}"
        )
        return "stuck", _worker_failure_summary(phase="planner", exc=exc), []
    return validate_plan_output(raw_result, allowed_kinds=allowed_kinds)


def _apply_item(
    *,
    chunk_file: Path,
    theory_file: Path,
    theorem_reuse_memory_file: Path,
    worker_settings: WorkerSettings,
    executor_prompt_file: Path,
    plan_item: dict[str, Any],
    pass_name: str,
    manifest_verify_timeout: int | None,
    pass_deadline_monotonic: float | None,
) -> dict[str, Any]:
    before_code = load_text(chunk_file)
    before_entries = build_derived_entries_from_file(chunk_file)
    prompt_text = load_prompt_text(executor_prompt_file)
    payload = _build_planner_payload(
        chunk_file=chunk_file,
        theory_file=theory_file,
        theorem_reuse_memory_file=theorem_reuse_memory_file,
    )
    payload["plan_item"] = plan_item
    payload["repair_round"] = 0
    item_id = str(plan_item.get("id", "")).strip() or "<no-id>"
    remaining_timeout_sec = _remaining_timeout_sec(pass_deadline_monotonic)
    if remaining_timeout_sec == 0:
        detail = (
            f"pass budget exhausted before apply started for {chunk_file.name} {pass_name} item={item_id}"
        )
        debug_log(f"[generated-local] {detail}")
        return {
            "applied": False,
            "result": "stuck",
            "summary": "apply budget exhausted",
            "change_notes": [detail],
            "touched_theorems": [],
            "item_id": str(plan_item.get("id", "")).strip(),
        }
    try:
        raw_result, _worker_meta = _run_with_heartbeat(
            label=(
                f"apply chunk={chunk_file.name} pass={pass_name} item={item_id}"
            ),
            timeout_sec=remaining_timeout_sec,
            fn=lambda: invoke_worker_json(
                settings=_scoped_worker_settings(worker_settings, remaining_timeout_sec),
                task_type="apply_derived_compression_item",
                system_prompt=prompt_text,
                payload=payload,
                metadata={
                    "input_file": str(chunk_file),
                    "pass_name": pass_name,
                    "item_id": str(plan_item.get("id", "")).strip(),
                },
            ),
        )
    except Exception as exc:
        detail = _single_line_excerpt(str(exc))
        debug_log(
            f"[generated-local] apply chunk={chunk_file.name} pass={pass_name} item={item_id} failed detail={detail}"
        )
        return {
            "applied": False,
            "result": "stuck",
            "summary": _worker_failure_summary(phase="apply", exc=exc),
            "change_notes": [detail] if detail else [],
            "touched_theorems": [],
            "item_id": str(plan_item.get("id", "")).strip(),
        }
    result, refactored_code, summary, change_notes, touched_theorems = validate_full_file_refactor_output(
        raw_result,
        label="generated local refactor output",
    )
    if result != "ok":
        return {
            "applied": False,
            "result": result,
            "summary": summary,
            "change_notes": change_notes,
            "touched_theorems": touched_theorems,
            "item_id": str(plan_item.get("id", "")).strip(),
        }

    after_entries = extract_theorem_entries_from_code(chunk_file, refactored_code)
    inventory_check = compare_theorem_inventories(before_entries, after_entries)
    if not bool(inventory_check.get("ok", False)):
        return {
            "applied": False,
            "result": "stuck",
            "summary": "inventory mismatch",
            "change_notes": change_notes,
            "touched_theorems": touched_theorems,
            "item_id": str(plan_item.get("id", "")).strip(),
            "inventory_check": inventory_check,
        }

    chunk_file.write_text(refactored_code.rstrip() + "\n", encoding="utf-8")
    manifest_timeout_sec = manifest_verify_timeout
    remaining_timeout_sec = _remaining_timeout_sec(pass_deadline_monotonic)
    if remaining_timeout_sec == 0:
        chunk_file.write_text(before_code.rstrip() + "\n", encoding="utf-8")
        return {
            "applied": False,
            "result": "stuck",
            "summary": "pass budget exhausted before manifest verification",
            "change_notes": change_notes,
            "touched_theorems": touched_theorems,
            "item_id": str(plan_item.get("id", "")).strip(),
        }
    if manifest_timeout_sec is None:
        manifest_timeout_sec = remaining_timeout_sec
    elif remaining_timeout_sec is not None:
        manifest_timeout_sec = min(manifest_timeout_sec, remaining_timeout_sec)
    manifest_result = _run_with_heartbeat(
        label=f"manifest-build chunk={chunk_file.name} pass={pass_name} item={item_id}",
        timeout_sec=manifest_timeout_sec,
        fn=lambda: _run_manifest_build(manifest_timeout_sec),
    )
    if not bool(manifest_result.get("success", False)):
        chunk_file.write_text(before_code.rstrip() + "\n", encoding="utf-8")
        return {
            "applied": False,
            "result": "stuck",
            "summary": "manifest verification failed",
            "change_notes": change_notes,
            "touched_theorems": touched_theorems,
            "item_id": str(plan_item.get("id", "")).strip(),
            "manifest_detail": str(manifest_result.get("detail", "")),
        }

    return {
        "applied": True,
        "result": result,
        "summary": summary,
        "change_notes": change_notes,
        "touched_theorems": touched_theorems,
        "item_id": str(plan_item.get("id", "")).strip(),
    }


def run_generated_local_passes(
    *,
    generated_root: Path,
    theory_file: Path,
    theorem_reuse_memory_file: Path,
    worker_command: str | None,
    worker_timeout: int | None,
    manifest_verify_timeout: int | None,
    max_rounds_per_pass: int,
) -> dict[str, Any]:
    worker_settings = resolve_refactor_worker_settings(
        worker_settings=None,
        worker_command=worker_command,
        worker_timeout=worker_timeout,
    )
    chunk_files = iter_generated_chunk_files(generated_root)
    chunk_reports: list[dict[str, Any]] = []
    applied_item_count = 0

    for chunk_file in chunk_files:
        debug_log(f"[generated-local] chunk={chunk_file}")
        per_chunk_reports: list[dict[str, Any]] = []
        for spec in PASS_SPECS:
            pass_name = str(spec["pass_name"])
            pass_timeout_sec = worker_settings.timeout_sec
            pass_deadline_monotonic = (
                None if pass_timeout_sec is None else time.monotonic() + pass_timeout_sec
            )
            debug_log(
                f"[generated-local] chunk={chunk_file.name} pass={pass_name} start "
                f"max_rounds={max_rounds_per_pass} timeout_budget={_timeout_label(pass_timeout_sec)}"
            )
            pass_report: dict[str, Any] = {"pass_name": pass_name, "rounds": []}
            for round_index in range(1, max_rounds_per_pass + 1):
                remaining_timeout_sec = _remaining_timeout_sec(pass_deadline_monotonic)
                if remaining_timeout_sec == 0:
                    detail = f"pass budget exhausted before round {round_index} for {chunk_file.name} {pass_name}"
                    debug_log(f"[generated-local] {detail}")
                    pass_report["rounds"].append(
                        {
                            "round": round_index,
                            "plan_result": "stuck",
                            "plan_summary": "pass budget exhausted",
                            "item_count": 0,
                        }
                    )
                    break
                debug_log(
                    f"[generated-local] chunk={chunk_file.name} pass={pass_name} round={round_index} "
                    f"planning remaining_timeout={_timeout_label(remaining_timeout_sec)}"
                )
                plan_result, plan_summary, plan_items = _plan_items(
                    chunk_file=chunk_file,
                    theory_file=theory_file,
                    theorem_reuse_memory_file=theorem_reuse_memory_file,
                    worker_settings=worker_settings,
                    prompt_file=Path(spec["prompt_file"]),
                    allowed_kinds=set(spec["allowed_kinds"]),
                    pass_name=pass_name,
                    pass_deadline_monotonic=pass_deadline_monotonic,
                )
                round_report: dict[str, Any] = {
                    "round": round_index,
                    "plan_result": plan_result,
                    "plan_summary": plan_summary,
                    "item_count": len(plan_items),
                }
                debug_log(
                    f"[generated-local] chunk={chunk_file.name} pass={pass_name} round={round_index} "
                    f"plan_result={plan_result} item_count={len(plan_items)}"
                )
                if plan_result != "ok" or not plan_items:
                    pass_report["rounds"].append(round_report)
                    break

                applied = False
                item_reports: list[dict[str, Any]] = []
                for item in plan_items:
                    item_id = str(item.get("id", "")).strip() or "<no-id>"
                    debug_log(
                        f"[generated-local] chunk={chunk_file.name} pass={pass_name} "
                        f"round={round_index} applying item={item_id}"
                    )
                    item_report = _apply_item(
                        chunk_file=chunk_file,
                        theory_file=theory_file,
                        theorem_reuse_memory_file=theorem_reuse_memory_file,
                        worker_settings=worker_settings,
                        executor_prompt_file=DEFAULT_EXECUTOR_PROMPT,
                        plan_item=item,
                        pass_name=pass_name,
                        manifest_verify_timeout=manifest_verify_timeout,
                        pass_deadline_monotonic=pass_deadline_monotonic,
                    )
                    item_reports.append(item_report)
                    debug_log(
                        f"[generated-local] chunk={chunk_file.name} pass={pass_name} "
                        f"round={round_index} item={item_id} applied={bool(item_report.get('applied', False))} "
                        f"result={item_report.get('result', '')}"
                    )
                    if bool(item_report.get("applied", False)):
                        applied = True
                        applied_item_count += 1
                        break
                round_report["items"] = item_reports
                pass_report["rounds"].append(round_report)
                if not applied:
                    break
            per_chunk_reports.append(pass_report)
            debug_log(f"[generated-local] chunk={chunk_file.name} pass={pass_name} done")
        chunk_reports.append({"chunk_file": str(chunk_file), "passes": per_chunk_reports})
        debug_log(f"[generated-local] chunk={chunk_file.name} done")

    return build_report(
        "ok",
        "completed",
        input_file=generated_root,
        output_file=generated_root,
        extra={
            "chunk_count": len(chunk_files),
            "applied_item_count": applied_item_count,
            "worker_timeout": worker_settings.timeout_sec,
            "chunk_reports": chunk_reports,
        },
    )


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Run local generated-file passes (pass1.2 then pass1.3) on each Generated chunk sequentially."
    )
    parser.add_argument("--generated-root", default=str(DEFAULT_GENERATED_ROOT))
    parser.add_argument("--theory-file", default=str(DEFAULT_THEORY))
    parser.add_argument("--theorem-reuse-memory-file", default=str(DEFAULT_THEOREM_REUSE_MEMORY))
    parser.add_argument("--worker-command")
    parser.add_argument("--worker-timeout", type=int, default=390)
    parser.add_argument("--manifest-verify-timeout", type=int, default=300)
    parser.add_argument("--max-rounds-per-pass", type=int, default=5)
    args = parser.parse_args()

    report = run_generated_local_passes(
        generated_root=Path(args.generated_root),
        theory_file=Path(args.theory_file),
        theorem_reuse_memory_file=Path(args.theorem_reuse_memory_file),
        worker_command=args.worker_command,
        worker_timeout=args.worker_timeout,
        manifest_verify_timeout=args.manifest_verify_timeout,
        max_rounds_per_pass=args.max_rounds_per_pass,
    )
    print_report(report)
    if report.get("status") == "error":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
