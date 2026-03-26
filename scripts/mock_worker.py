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
        "lean_statement": stmt,
        "theorem_name_stem": "statement_target" if stmt else "",
        "docstring_summary": "Mock theorem statement" if stmt else "",
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
    tracked = payload.get("tracked_problems", [])
    priorities: list[dict[str, str]] = []
    if isinstance(tracked, list):
        for item in tracked:
            if not isinstance(item, dict):
                continue
            problem_id = str(item.get("problem_id", "")).strip()
            if not problem_id:
                continue
            priorities.append(
                {
                    "problem_id": problem_id,
                    "priority": "medium",
                    "rationale": "mock_worker: default medium priority",
                }
            )
    return {"priorities": priorities}


def _refactor_derived_result(payload: dict[str, Any]) -> dict[str, Any]:
    derived_code = str(payload.get("derived_code", "")).strip()
    return {
        "result": "ok" if derived_code else "stuck",
        "refactored_code": derived_code,
        "summary": "mock_worker: echoed input Derived.lean" if derived_code else "mock_worker: no Derived.lean content provided",
        "change_notes": ["mock_worker: no refactor applied"] if derived_code else [],
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
        elif task_type == "refactor_derived":
            result_payload = _refactor_derived_result(payload)
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
