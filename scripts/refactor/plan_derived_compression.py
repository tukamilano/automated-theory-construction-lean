from __future__ import annotations

import argparse
import sys
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
from common import write_json_atomic
from derived_refactor_utils import build_exact_duplicate_statement_groups
from derived_refactor_utils import build_report
from derived_refactor_utils import debug_log
from derived_refactor_utils import load_prompt_text
from derived_refactor_utils import load_text
from derived_refactor_utils import print_report
from derived_refactor_utils import resolve_refactor_worker_settings
from theorem_reuse_memory import load_theorem_reuse_memory
from theorem_reuse_memory import summarize_supporting_theorem_frequency
from worker_client import WorkerSettings
from worker_client import invoke_worker_json


DEFAULT_INPUT = Path("AutomatedTheoryConstruction/Derived.refactored.preview.lean")
DEFAULT_PLAN = Path("AutomatedTheoryConstruction/Derived.compression.plan.json")
DEFAULT_PROMPT = Path("prompts/derived/compression_planner.md")
DEFAULT_THEORY = Path("AutomatedTheoryConstruction/Theory.lean")
DEFAULT_THEOREM_REUSE_MEMORY = loop_theorem_reuse_memory_path(Path("data"))

VALID_ITEM_KINDS = {
    "exact_duplicate_collapse",
    "proof_retarget",
    "cluster_reorder",
    "cluster_sectionize",
}


def _clean_string_list(raw: Any, *, max_items: int | None = None) -> list[str]:
    if not isinstance(raw, list):
        return []
    items = [str(item).strip() for item in raw if str(item).strip()]
    return items[:max_items] if max_items is not None else items


def validate_plan_output(
    payload: dict[str, Any],
    *,
    allowed_kinds: set[str],
) -> tuple[str, str, list[dict[str, Any]]]:
    required_keys = {"result", "summary", "items"}
    if set(payload.keys()) != required_keys:
        raise ValueError("planner output must contain exactly: result, summary, items")

    result = str(payload.get("result", "")).strip()
    summary = str(payload.get("summary", "")).strip()
    items = payload.get("items")
    if result not in {"ok", "noop", "stuck"}:
        raise ValueError("planner result must be one of: ok, noop, stuck")
    if not isinstance(items, list):
        raise ValueError("planner items must be a list")

    cleaned_items: list[dict[str, Any]] = []
    for index, item in enumerate(items[:5], start=1):
        if not isinstance(item, dict):
            raise ValueError("planner items must contain only objects")
        kind = str(item.get("kind", "")).strip()
        if kind not in VALID_ITEM_KINDS:
            raise ValueError(f"planner item kind is invalid: {kind}")
        if kind not in allowed_kinds:
            raise ValueError(f"planner item kind is not allowed for this pass: {kind}")
        item_id = str(item.get("id", f"item_{index:03d}")).strip() or f"item_{index:03d}"
        cleaned_item = {
            "id": item_id,
            "kind": kind,
            "anchor_theorems": _clean_string_list(item.get("anchor_theorems", []), max_items=8),
            "rewrite_targets": _clean_string_list(item.get("rewrite_targets", []), max_items=8),
            "new_theorems": _clean_string_list(item.get("new_theorems", []), max_items=1),
            "local_reorder_region": _clean_string_list(item.get("local_reorder_region", []), max_items=8),
            "section_title": str(item.get("section_title", "")).strip(),
            "section_members": _clean_string_list(item.get("section_members", []), max_items=12),
            "insert_before": str(item.get("insert_before", "")).strip(),
            "expected_benefit": str(item.get("expected_benefit", "")).strip(),
        }
        if kind == "cluster_sectionize":
            if not cleaned_item["section_title"]:
                raise ValueError("cluster_sectionize items must provide a non-empty section_title")
            if not cleaned_item["insert_before"]:
                raise ValueError("cluster_sectionize items must provide a non-empty insert_before")
            if len(cleaned_item["section_members"]) < 2:
                raise ValueError("cluster_sectionize items must provide at least two section_members")
            if cleaned_item["insert_before"] not in cleaned_item["section_members"]:
                cleaned_item["section_members"] = [cleaned_item["insert_before"], *cleaned_item["section_members"]]
        cleaned_items.append(cleaned_item)

    if result != "ok" and cleaned_items:
        raise ValueError("planner items must be empty unless result=ok")
    return result, summary, cleaned_items


def build_payload(
    *,
    input_file: Path,
    theory_file: Path,
    derived_code: str,
    theory_context: str,
    theorem_inventory: list[dict[str, str]],
    theorem_reuse_memory: list[dict[str, Any]],
    supporting_theorem_frequency: list[dict[str, Any]],
) -> dict[str, Any]:
    return {
        "input_file": str(input_file),
        "theory_file": str(theory_file),
        "derived_code": derived_code,
        "theory_context": theory_context,
        "theorem_inventory": theorem_inventory,
        "exact_duplicate_statement_groups": build_exact_duplicate_statement_groups(theorem_inventory),
        "supporting_theorem_frequency": supporting_theorem_frequency[:20],
        "theorem_reuse_memory": theorem_reuse_memory[-12:],
    }


def run_plan_derived_compression(
    *,
    input_file: Path,
    theory_file: Path,
    prompt_file: Path,
    theorem_reuse_memory_file: Path,
    output_file: Path,
    worker_settings: WorkerSettings | None = None,
    worker_command: str | None = None,
    worker_timeout: int | None = None,
    allowed_kinds: set[str] | None = None,
) -> dict[str, Any]:
    try:
        if not allowed_kinds:
            raise ValueError("allowed_kinds must be non-empty")
        prompt_text = load_prompt_text(prompt_file)
        derived_code = load_text(input_file)
        _, theory_context = load_theory_context(theory_file)
        theorem_inventory = build_derived_entries_from_file(input_file)
        theorem_reuse_memory = load_theorem_reuse_memory(theorem_reuse_memory_file)
        supporting_theorem_frequency = summarize_supporting_theorem_frequency(theorem_reuse_memory)

        worker_settings = resolve_refactor_worker_settings(
            worker_settings=worker_settings,
            worker_command=worker_command,
            worker_timeout=worker_timeout,
        )

        payload = build_payload(
            input_file=input_file,
            theory_file=theory_file,
            derived_code=derived_code,
            theory_context=theory_context,
            theorem_inventory=theorem_inventory,
            theorem_reuse_memory=theorem_reuse_memory,
            supporting_theorem_frequency=supporting_theorem_frequency,
        )
        debug_log(
            "Planning derived compression: "
            f"input={input_file} output={output_file} "
            f"worker_timeout={'none' if worker_settings.timeout_sec is None else worker_settings.timeout_sec}"
        )
        raw_result, _worker_meta = invoke_worker_json(
            settings=worker_settings,
            task_type="plan_derived_compression",
            system_prompt=prompt_text,
            payload=payload,
            metadata={"input_file": str(input_file)},
        )
        result, summary, items = validate_plan_output(raw_result, allowed_kinds=allowed_kinds)
        plan_payload = {
            "plan_version": 1,
            "source_file": str(input_file),
            "summary": summary,
            "items": items if result == "ok" else [],
        }
        write_json_atomic(output_file, plan_payload)
        return build_report(
            "ok" if result == "ok" else "noop",
            "completed" if result == "ok" else "no_candidates",
            stop_detail="" if result == "ok" else "planner returned no items",
            input_file=input_file,
            output_file=output_file,
            extra={
                "result": result,
                "summary": summary,
                "item_count": len(plan_payload["items"]),
            },
        )
    except Exception as exc:
        return build_report(
            "error",
            "worker_error",
            stop_detail=str(exc),
            input_file=input_file,
            output_file=output_file,
            extra={
                "result": "stuck",
                "summary": "",
                "item_count": 0,
            },
        )


def main() -> None:
    parser = argparse.ArgumentParser(description="Plan a small soft-compression pass for Derived.refactored.preview.lean")
    parser.add_argument("--input-file", default=str(DEFAULT_INPUT))
    parser.add_argument("--theory-file", default=str(DEFAULT_THEORY))
    parser.add_argument("--prompt-file", default=str(DEFAULT_PROMPT))
    parser.add_argument("--theorem-reuse-memory-file", default=str(DEFAULT_THEOREM_REUSE_MEMORY))
    parser.add_argument("--output-file", default=str(DEFAULT_PLAN))
    parser.add_argument("--worker-command")
    parser.add_argument("--worker-timeout", type=int)
    args = parser.parse_args()

    report = run_plan_derived_compression(
        input_file=Path(args.input_file),
        theory_file=Path(args.theory_file),
        prompt_file=Path(args.prompt_file),
        theorem_reuse_memory_file=Path(args.theorem_reuse_memory_file),
        output_file=Path(args.output_file),
        worker_command=args.worker_command,
        worker_timeout=args.worker_timeout,
        allowed_kinds={"exact_duplicate_collapse"},
    )
    print_report(report)
    if report.get("status") == "error":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
