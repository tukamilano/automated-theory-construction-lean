from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

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


REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_THEORY = Path("AutomatedTheoryConstruction/Theory.lean")
DEFAULT_THEOREM_REUSE_MEMORY = Path("data/theorem_reuse_memory.json")
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
) -> tuple[str, str, list[dict[str, Any]]]:
    prompt_text = load_prompt_text(prompt_file)
    payload = _build_planner_payload(
        chunk_file=chunk_file,
        theory_file=theory_file,
        theorem_reuse_memory_file=theorem_reuse_memory_file,
    )
    raw_result, _worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="plan_derived_compression",
        system_prompt=prompt_text,
        payload=payload,
        metadata={"input_file": str(chunk_file), "pass_name": pass_name},
    )
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
    raw_result, _worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="apply_derived_compression_item",
        system_prompt=prompt_text,
        payload=payload,
        metadata={
            "input_file": str(chunk_file),
            "pass_name": pass_name,
            "item_id": str(plan_item.get("id", "")).strip(),
        },
    )
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
    manifest_result = _run_manifest_build(manifest_verify_timeout)
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
            pass_report: dict[str, Any] = {"pass_name": pass_name, "rounds": []}
            for round_index in range(1, max_rounds_per_pass + 1):
                plan_result, plan_summary, plan_items = _plan_items(
                    chunk_file=chunk_file,
                    theory_file=theory_file,
                    theorem_reuse_memory_file=theorem_reuse_memory_file,
                    worker_settings=worker_settings,
                    prompt_file=Path(spec["prompt_file"]),
                    allowed_kinds=set(spec["allowed_kinds"]),
                    pass_name=pass_name,
                )
                round_report: dict[str, Any] = {
                    "round": round_index,
                    "plan_result": plan_result,
                    "plan_summary": plan_summary,
                    "item_count": len(plan_items),
                }
                if plan_result != "ok" or not plan_items:
                    pass_report["rounds"].append(round_report)
                    break

                applied = False
                item_reports: list[dict[str, Any]] = []
                for item in plan_items:
                    item_report = _apply_item(
                        chunk_file=chunk_file,
                        theory_file=theory_file,
                        theorem_reuse_memory_file=theorem_reuse_memory_file,
                        worker_settings=worker_settings,
                        executor_prompt_file=DEFAULT_EXECUTOR_PROMPT,
                        plan_item=item,
                        pass_name=pass_name,
                        manifest_verify_timeout=manifest_verify_timeout,
                    )
                    item_reports.append(item_report)
                    if bool(item_report.get("applied", False)):
                        applied = True
                        applied_item_count += 1
                        break
                round_report["items"] = item_reports
                pass_report["rounds"].append(round_report)
                if not applied:
                    break
            per_chunk_reports.append(pass_report)
        chunk_reports.append({"chunk_file": str(chunk_file), "passes": per_chunk_reports})

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
