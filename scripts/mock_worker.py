from __future__ import annotations

import json
from pathlib import Path
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


def _headline_theorem_generate_result(payload: dict[str, Any]) -> dict[str, Any]:
    candidate_set_id = str(payload.get("candidate_set_id", ""))
    return {
        "candidate_set_id": candidate_set_id,
        "candidates": [
            {
                "candidate_rank_seed": 1,
                "statement": "True",
                "theorem_name_stem": "mock_headline_theorem_summary",
                "docstring_summary": "Mock summary theorem target.",
                "rationale": "mock_worker: placeholder structural summary candidate",
                "supporting_theorems": [],
                "missing_lemmas": [],
                "source_problem_ids": [],
                "theorem_pattern": "structure_discovery",
                "context_note": "mock_worker: candidate 1 summarises the visible tracked problem family",
                "conceptual_depth_note": "mock_worker: candidate 1 is framed as a structural summary rather than a local technical step",
            },
            {
                "candidate_rank_seed": 2,
                "statement": "True -> True",
                "theorem_name_stem": "mock_headline_theorem_bridge",
                "docstring_summary": "Mock bridge theorem target.",
                "rationale": "mock_worker: placeholder bridge-style candidate",
                "supporting_theorems": [],
                "missing_lemmas": [],
                "source_problem_ids": [],
                "theorem_pattern": "new_theorem",
                "context_note": "mock_worker: candidate 2 is positioned as the strongest placeholder title-level result",
                "conceptual_depth_note": "mock_worker: candidate 2 is framed around a reusable bridge rather than bookkeeping",
            },
            {
                "candidate_rank_seed": 3,
                "statement": "True ∧ True",
                "theorem_name_stem": "mock_headline_theorem_framework",
                "docstring_summary": "Mock framework theorem target.",
                "rationale": "mock_worker: placeholder framework-style candidate",
                "supporting_theorems": [],
                "missing_lemmas": [],
                "source_problem_ids": [],
                "theorem_pattern": "framework_introduction",
                "context_note": "mock_worker: candidate 3 is positioned as a framework consequence of the visible theory",
                "conceptual_depth_note": "mock_worker: candidate 3 is framed as a conceptual interface rather than a technical extension",
            },
        ],
    }


def _headline_theorem_select_result(payload: dict[str, Any]) -> dict[str, Any]:
    candidate_set_id = str(payload.get("candidate_set_id", ""))
    candidates = payload.get("candidates", [])
    candidate_rank_seeds = [
        int(item.get("candidate_rank_seed", 0))
        for item in candidates
        if isinstance(item, dict) and isinstance(item.get("candidate_rank_seed"), int)
    ]
    selected_candidate_rank_seed = 2 if 2 in candidate_rank_seeds else (candidate_rank_seeds[0] if candidate_rank_seeds else 1)
    ranking: list[dict[str, Any]] = []
    for rank, candidate_rank_seed in enumerate(
        [selected_candidate_rank_seed] + [seed for seed in candidate_rank_seeds if seed != selected_candidate_rank_seed],
        start=1,
    ):
        ranking.append(
            {
                "candidate_rank_seed": candidate_rank_seed,
                "rank": rank,
                "decision": "select" if rank == 1 else "reject",
                "reason": (
                    "mock_worker: selected as the strongest placeholder title-level theorem"
                    if rank == 1
                    else f"mock_worker: ranked below the selected placeholder candidate at rank {rank}"
                ),
            }
        )
    return {
        "candidate_set_id": candidate_set_id,
        "selected_candidate_rank_seed": selected_candidate_rank_seed,
        "selection_summary": "mock_worker: choose the strongest placeholder candidate from the fixed candidate set",
        "ranking": ranking,
    }


def _headline_theorem_suggest_result(payload: dict[str, Any]) -> dict[str, Any]:
    candidate_id = str(payload.get("candidate_id", ""))
    return {
        "candidate_id": candidate_id,
        "result": "ok",
        "statement": "True -> True",
        "theorem_name_stem": "mock_headline_theorem_bridge",
        "docstring_summary": "Mock bridge theorem target.",
        "rationale": "mock_worker: placeholder bridge-style candidate",
        "supporting_theorems": [],
        "missing_lemmas": [],
        "source_problem_ids": [],
        "theorem_pattern": "new_theorem",
        "context_note": "mock_worker: candidate is positioned as a title-level structural bridge",
        "conceptual_depth_note": "mock_worker: candidate is framed around a reusable bridge rather than bookkeeping",
    }


def _headline_theorem_retrieve_result(payload: dict[str, Any]) -> dict[str, Any]:
    candidate_id = str(payload.get("candidate_id", ""))
    return {
        "candidate_id": candidate_id,
        "closest_items": [
            {
                "reference": "mock source link",
                "kind": "source_link",
                "relevance": "mock_worker: nearest placeholder structural-theory anchor",
                "confidence": "medium",
            }
        ],
        "research_line": "mock_worker: structural summary and bridge theorems in the visible theory neighborhood",
        "coverage_assessment": "mock_worker: one placeholder anchor is enough for mock retrieval",
        "missing_angles": [],
        "need_supplemental_retrieval": False,
    }


def _headline_theorem_map_result(payload: dict[str, Any]) -> dict[str, Any]:
    candidate_id = str(payload.get("candidate_id", ""))
    return {
        "candidate_id": candidate_id,
        "closest_baseline": "mock baseline theorem",
        "relations": [
            {
                "reference": "mock source link",
                "overlap": "mock_worker: both concern the same broad structural theme",
                "delta": "mock_worker: candidate is framed as a stronger structural bridge",
                "delta_materiality": "unclear",
            }
        ],
        "overall_novelty_risk": "medium",
        "variant_objection": "mock_worker: this could still look like a nearby variant without stronger evidence",
    }


def _headline_theorem_evaluate_result(payload: dict[str, Any]) -> dict[str, Any]:
    candidate_id = str(payload.get("candidate_id", ""))
    return {
        "candidate_id": candidate_id,
        "baseline_delta_supported": "yes",
        "novelty": "medium",
        "significance": "medium",
        "paper_unit_viability": "yes",
        "conciseness": "yes",
        "strongest_positive_signal": "mock_worker: the theorem is the cleanest available summary of the visible bridge structure",
        "strongest_objection": "mock_worker: the theorem may still look too close to a visible baseline",
        "objection_answerable": "yes",
        "minimal_publishable_unit": "mock_worker: a short structural note centered on the bridge theorem and its nearest corollaries",
        "salvage_plan": "mock_worker: add sharper comparisons if stricter review is needed",
        "rejection_tags": [],
        "verdict": "pass",
        "reason": "mock_worker: pass the strongest placeholder candidate in mock mode",
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
        elif task_type == "post_theorem_expand":
            result_payload = _post_theorem_expand_result(payload)
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
