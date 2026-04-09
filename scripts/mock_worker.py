from __future__ import annotations

import json
import sys
from typing import Any


def _read_request() -> dict[str, Any]:
    raw = sys.stdin.read()
    payload = json.loads(raw)
    if not isinstance(payload, dict):
        raise ValueError("request must be a JSON object")
    return payload

def _prover_result(payload: dict[str, Any]) -> dict[str, Any]:
    problem_id = str(payload.get("problem_id", ""))
    return {
        "problem_id": problem_id,
        "result": "stuck",
        "proof_sketch": "mock_worker: no proof attempt",
        "counterexample_text": "mock_worker: no proof generated",
        "new_problems": [],
    }


def _prover_statement_result(payload: dict[str, Any]) -> dict[str, Any]:
    problem_id = str(payload.get("problem_id", ""))
    stmt = str(payload.get("stmt", "")).strip()
    return {
        "problem_id": problem_id,
        "result": "ok" if stmt else "stuck",
        "statement_prelude_code": "",
        "lean_statement": stmt,
        "theorem_name_stem": "statement_target" if stmt else "",
        "docstring_summary": "Mock echoed statement." if stmt else "",
        "notes": "mock_worker: echoed input statement" if stmt else "mock_worker: no statement provided",
    }


def _formalize_result(payload: dict[str, Any]) -> dict[str, Any]:
    problem_id = str(payload.get("problem_id", ""))
    requested_result = str(payload.get("result", "stuck"))
    if requested_result not in {"proof", "counterexample", "stuck"}:
        requested_result = "stuck"

    return {
        "problem_id": problem_id,
        "result": requested_result,
        "proof_sketch": str(payload.get("proof_sketch", "")),
        "prelude_code": "",
        "proof_text": "",
        "counterexample_text": str(payload.get("counterexample_text", "")),
    }


def _repair_result(payload: dict[str, Any]) -> dict[str, Any]:
    problem_id = str(payload.get("problem_id", ""))
    previous_result = str(payload.get("previous_result", "stuck"))
    if previous_result not in {"proof", "counterexample", "stuck"}:
        previous_result = "stuck"

    return {
        "problem_id": problem_id,
        "result": previous_result,
        "proof_sketch": str(payload.get("previous_proof_sketch", "")),
        "prelude_code": str(payload.get("previous_prelude_code", "")),
        "proof_text": str(payload.get("previous_proof_text", "")),
        "counterexample_text": str(payload.get("previous_counterexample_text", "")),
    }


def _expand_result(payload: dict[str, Any]) -> dict[str, Any]:
    problem_id = str(payload.get("problem_id", ""))
    return {
        "problem_id": problem_id,
        "candidates": [],
    }


def _prioritize_open_problems_result(payload: dict[str, Any]) -> dict[str, Any]:
    tracked_problems = payload.get("tracked_problems", [])
    if not isinstance(tracked_problems, list):
        tracked_problems = []
    return {
        "priorities": [
            {
                "problem_id": str(item.get("problem_id", "")).strip(),
                "priority": "medium",
                "rationale": "mock_worker: neutral priority refresh",
            }
            for item in tracked_problems
            if isinstance(item, dict) and str(item.get("problem_id", "")).strip()
        ],
        "theory_snapshot": "Mock theory state: no reliable global interpretation is available, so only a minimal exploratory snapshot is recorded.",
        "next_direction": {
            "label": "mock_direction",
            "guidance": "Prefer neutral exploratory problems in mock mode.",
            "rationale": "Mock worker does not compute a real global direction.",
        },
        "desired_summary_changes": [],
        "current_bottlenecks": [],
        "overexplored_patterns": [],
        "missing_bridges": [],
        "agenda_pressure": [],
    }


def _main_theorem_suggest_result(payload: dict[str, Any]) -> dict[str, Any]:
    candidate_id = str(payload.get("candidate_id", ""))
    return {
        "candidate_id": candidate_id,
        "result": "stuck",
        "statement": "",
        "theorem_name_stem": "",
        "docstring_summary": "",
        "rationale": "mock_worker: no main theorem suggestion",
        "supporting_theorems": [],
        "missing_lemmas": [],
    }


def _main_theorem_plan_result(payload: dict[str, Any]) -> dict[str, Any]:
    candidate_id = str(payload.get("candidate_id", ""))
    return {
        "candidate_id": candidate_id,
        "result": "stuck",
        "plan_summary": "mock_worker: no plan generated",
        "proof_sketch": "",
        "supporting_theorems": [],
        "intermediate_lemmas": [],
        "notes": "mock_worker: no main theorem proof plan",
    }


def _post_theorem_expand_result(payload: dict[str, Any]) -> dict[str, Any]:
    problem_id = str(payload.get("problem_id", ""))
    return {
        "problem_id": problem_id,
        "candidates": [],
    }


def _refactor_derived_result(payload: dict[str, Any]) -> dict[str, Any]:
    derived_code = str(payload.get("derived_code", "")).strip()
    focus_theorem_names = [
        str(item).strip()
        for item in payload.get("focus_theorem_names", [])
        if str(item).strip()
    ]
    return {
        "result": "noop" if derived_code else "stuck",
        "refactored_code": derived_code,
        "summary": "mock_worker: no local refactor applied" if derived_code else "mock_worker: no Derived.lean content provided",
        "change_notes": ["mock_worker: returned input unchanged"] if derived_code else [],
        "touched_theorems": focus_theorem_names,
    }


def _plan_derived_compression_result(payload: dict[str, Any]) -> dict[str, Any]:
    theorem_inventory = payload.get("theorem_inventory", [])
    return {
        "result": "noop" if isinstance(theorem_inventory, list) else "stuck",
        "summary": "mock_worker: no compression plan generated" if isinstance(theorem_inventory, list) else "mock_worker: invalid theorem inventory",
        "items": [],
    }


def _apply_derived_compression_item_result(payload: dict[str, Any]) -> dict[str, Any]:
    derived_code = str(payload.get("derived_code", "")).strip()
    plan_item = payload.get("plan_item", {})
    touched_theorems = []
    if isinstance(plan_item, dict):
        for key in ("anchor_theorems", "rewrite_targets", "new_theorems", "local_reorder_region", "section_members"):
            raw = plan_item.get(key, [])
            if not isinstance(raw, list):
                continue
            for item in raw:
                cleaned = str(item).strip()
                if cleaned and cleaned not in touched_theorems:
                    touched_theorems.append(cleaned)
        insert_before = str(plan_item.get("insert_before", "")).strip()
        if insert_before and insert_before not in touched_theorems:
            touched_theorems.append(insert_before)
    return {
        "result": "noop" if derived_code else "stuck",
        "refactored_code": derived_code,
        "summary": "mock_worker: no compression item applied" if derived_code else "mock_worker: no Derived.lean content provided",
        "change_notes": ["mock_worker: returned input unchanged"] if derived_code else [],
        "touched_theorems": touched_theorems,
    }


def main() -> None:
    try:
        request = _read_request()
        task_type = str(request.get("task_type", "")).strip()
        payload = request.get("payload", {})
        if not isinstance(payload, dict):
            raise ValueError("payload must be a JSON object")

        if task_type == "prover_statement":
            result_payload = _prover_statement_result(payload)
        elif task_type == "prover":
            result_payload = _prover_result(payload)
        elif task_type == "formalize":
            result_payload = _formalize_result(payload)
        elif task_type == "repair":
            result_payload = _repair_result(payload)
        elif task_type == "expand":
            result_payload = _expand_result(payload)
        elif task_type == "prioritize_open_problems":
            result_payload = _prioritize_open_problems_result(payload)
        elif task_type == "main_theorem_suggest":
            result_payload = _main_theorem_suggest_result(payload)
        elif task_type == "main_theorem_plan":
            result_payload = _main_theorem_plan_result(payload)
        elif task_type == "post_theorem_expand":
            result_payload = _post_theorem_expand_result(payload)
        elif task_type == "refactor_derived":
            result_payload = _refactor_derived_result(payload)
        elif task_type == "plan_derived_compression":
            result_payload = _plan_derived_compression_result(payload)
        elif task_type == "apply_derived_compression_item":
            result_payload = _apply_derived_compression_item_result(payload)
        else:
            raise ValueError(f"unsupported task_type: {task_type}")

        raw_model_output = json.dumps(result_payload, ensure_ascii=False)
        response = {
            "result_payload": result_payload,
            "worker_meta": {
                "worker": "mock_worker",
                "task_type": task_type,
                "raw_model_output": raw_model_output,
            },
            "error": None,
        }
    except Exception as exc:
        response = {
            "result_payload": {},
            "worker_meta": {"worker": "mock_worker"},
            "error": str(exc),
        }

    sys.stdout.write(json.dumps(response, ensure_ascii=False))


if __name__ == "__main__":
    main()
