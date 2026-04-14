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


def _problem_design_core_extract_result(payload: dict[str, Any]) -> dict[str, Any]:
    problem_id = str(payload.get("problem_id", ""))
    cluster_context = payload.get("cluster_context", {})
    selected_cluster_id = str(cluster_context.get("cluster_id", "")).strip() or "cluster_001"
    closest_baseline = ""
    if isinstance(cluster_context, dict):
        external_positioning = cluster_context.get("external_positioning", {})
        if isinstance(external_positioning, dict):
            closest_baselines = external_positioning.get("closest_baselines", [])
            if isinstance(closest_baselines, list) and closest_baselines and isinstance(closest_baselines[0], dict):
                closest_baseline = str(closest_baselines[0].get("reference", "")).strip()
    return {
        "problem_id": problem_id,
        "cluster_id": selected_cluster_id,
        "headline_claim": "Every admissible partial elimination state computes the same intrinsic semantic object on the remaining reachable region.",
        "core_mathematical_content": "The visible semantic presentations share one intrinsic partial-state invariant rather than merely agreeing at the final endpoint.",
        "literature_context": {
            "closest_baseline": closest_baseline or "mock baseline on structural saturation",
            "routine_reading_risk": "A weaker face could be dismissed as order-insensitive execution packaging.",
            "possible_opening": "The cluster still supports a theorem face centered on an intrinsic partial-state semantic invariant.",
        },
        "supporting_claims": [
            "Final-state uniqueness is a corollary of the partial-state invariant.",
            "Terminal-frontier summaries fail to capture the same invariant.",
        ],
        "no_go_faces": [
            "fold correctness as the headline theorem",
            "giant equivalence package over every visible semantic view",
        ],
        "proof_assets": [
            "bounded convergence",
            "reverse-topological execution details",
        ],
        "why_this_face": "mock_worker: this is the cleanest dossier face that keeps execution machinery in the support layer",
    }


def _problem_design_cluster_result(payload: dict[str, Any]) -> dict[str, Any]:
    derived_theorems = payload.get("derived_theorems", [])
    member_theorems: list[dict[str, str]] = []
    if isinstance(derived_theorems, list):
        for raw_item in derived_theorems[:2]:
            if not isinstance(raw_item, dict):
                continue
            theorem_name = str(raw_item.get("name", "")).strip()
            theorem_statement = str(raw_item.get("statement", "")).strip()
            if theorem_name and theorem_statement:
                member_theorems.append({"name": theorem_name, "statement": theorem_statement})
    if not member_theorems:
        member_theorems = [{"name": "mock_visible_theorem", "statement": "True"}]
    return {
        "clusters": [
            {
                "cluster_id": "cluster_001",
                "cluster_theme": "canonical semantic equivalence",
                "cluster_summary": "Visible results already orbit one equivalence-style semantic family.",
                "member_theorems": member_theorems,
                "objects": ["reachable region", "fold semantics"],
                "invariants": ["semantic equivalence", "stabilization"],
                "algorithms": ["reverse sweep"],
                "suspected_support_layer": ["bounded convergence", "execution-order bookkeeping"],
            }
        ]
    }


def _problem_design_contextualize_result(payload: dict[str, Any]) -> dict[str, Any]:
    cluster_id = str(payload.get("cluster_id", "cluster_001"))
    cluster = payload.get("cluster", {})
    cluster_theme = str(cluster.get("cluster_theme", "")).strip() if isinstance(cluster, dict) else ""
    if not cluster_theme:
        cluster_theme = "canonical semantic equivalence"
    return {
        "cluster_id": cluster_id,
        "cluster_theme": cluster_theme,
        "internal_state_assessment": {
            "already_settled_claims": ["mock_worker: multiple views of the same semantic object already appear visible"],
            "support_layer_claims": ["mock_worker: bounded convergence and schedule control look support-layer"],
            "claims_that_now_look_like_packaging": ["mock_worker: bundling every visible equivalence into one headline theorem"],
            "internal_packaging_risk": "medium",
        },
        "external_positioning": {
            "closest_baselines": [
                {
                    "reference": "mock baseline on canonical proof representations",
                    "what_it_already_owns": "mock_worker: broad order-insensitivity and canonicalization pressure",
                    "evidence_strength": "summary",
                    "danger_level": "medium",
                }
            ],
            "baseline_summary": "mock_worker: literature already pressures broad canonicalization stories",
            "unresolved_baseline_risks": ["mock_worker: theorem-level delta still needs to be sharper than generic canonicalization"],
            "external_baseline_pressure": "medium",
        },
        "paper_core_analysis": {
            "no_go_faces": ["mock_worker: execution-order packaging theorem", "mock_worker: giant conjunction of equivalent views"],
            "possible_gap_types": ["semantic boundary", "canonical classifier"],
            "most_plausible_gap": "mock_worker: one clean equivalence or boundary statement inside the cluster",
            "gap_rationale": "mock_worker: the cluster still suggests one theorem-level conceptual core",
            "headline_viability": "promising",
        },
        "proposal_guidance": {
            "allowed_headline_directions": ["mock_worker: direct semantic equivalence", "mock_worker: sharp canonicality boundary"],
            "discouraged_headline_directions": ["mock_worker: support-layer convergence bundle"],
            "must_clear_for_novelty": ["mock_worker: show a sharper delta than broad proof-order canonicalization"],
        },
    }


def _paper_claim_retrieve_result(payload: dict[str, Any]) -> dict[str, Any]:
    problem_id = str(payload.get("problem_id", ""))
    return {
        "problem_id": problem_id,
        "closest_items": [
            {
                "reference": "mock source link",
                "kind": "source_link",
                "relevance": "mock_worker: nearest external anchor for this dossier",
                "confidence": "medium",
            }
        ],
        "directly_read_evidence": [
            {
                "reference": "mock source link",
                "evidence": "mock_worker: directly read material pressures broad canonicalization but not this exact theorem face",
                "supports": "some external novelty room remains if the theorem face stays sharp",
                "confidence": "medium",
            }
        ],
        "coverage_assessment": "mock_worker: one placeholder direct-reading anchor is enough in mock mode",
        "missing_angles": [],
        "need_supplemental_retrieval": False,
    }


def _paper_claim_select_result(payload: dict[str, Any]) -> dict[str, Any]:
    selection_id = str(payload.get("selection_id", ""))
    dossier_packages = payload.get("dossier_packages", [])
    assessments: list[dict[str, Any]] = []
    selected_problem_id = "pd_paper_claim_01"
    if isinstance(dossier_packages, list):
        for index, item in enumerate(dossier_packages, start=1):
            if not isinstance(item, dict):
                continue
            problem_id = str(item.get("problem_id", "")).strip()
            if not problem_id:
                continue
            if not assessments:
                selected_problem_id = problem_id
            assessments.append(
                {
                    "problem_id": problem_id,
                    "paper_publishable_fit": "high" if index == 1 else "medium",
                    "selected": index == 1,
                    "why_selected": "mock_worker: strongest current paper-facing dossier in mock mode" if index == 1 else "",
                    "why_not_selected": "" if index == 1 else "mock_worker: still plausibly paper-facing, but not as publishable as the selected dossier",
                }
            )
    if not assessments:
        assessments = [
            {
                "problem_id": selected_problem_id,
                "paper_publishable_fit": "medium",
                "selected": True,
                "why_selected": "mock_worker: placeholder dossier",
                "why_not_selected": "",
            }
        ]
    return {
        "selection_id": selection_id,
        "selected_problem_id": selected_problem_id,
        "selection_note": "mock_worker: choose the dossier with the best current paper-publishable fit",
        "planning_focus": "mock_worker: plan this as a short theorem package centered on the cleanest theorem face",
        "assessments": assessments,
    }


def _paper_claim_map_result(payload: dict[str, Any]) -> dict[str, Any]:
    problem_id = str(payload.get("problem_id", ""))
    return {
        "problem_id": problem_id,
        "closest_baseline": "mock baseline on canonical proof representations",
        "relations": [
            {
                "reference": "mock source link",
                "overlap": "mock_worker: both live in the same broad canonicalization neighborhood",
                "delta": "mock_worker: the dossier still claims a sharper theorem face than the baseline summary itself states",
                "delta_materiality": "unclear",
            }
        ],
        "theorem_face_assessment": "mock_worker: the face is plausible if execution packaging stays subordinate",
        "baseline_delta": "mock_worker: the candidate must be sold as a theorem boundary, not as another sweep implementation",
        "outsider_risk": "mock_worker: an outsider may still read this as canonicalization repackaging",
    }


def _paper_claim_plan_result(payload: dict[str, Any]) -> dict[str, Any]:
    plan_id = str(payload.get("plan_id", ""))
    selected_dossier_package = payload.get("selected_dossier_package", {})
    selected_problem_id = "pd_paper_claim_01"
    headline = "Exact residual acceptance is controlled by one intrinsic global classifier."
    if isinstance(selected_dossier_package, dict):
        selected_problem_id = str(selected_dossier_package.get("problem_id", "")).strip() or selected_problem_id
        dossier = selected_dossier_package.get("dossier", {})
        if isinstance(dossier, dict):
            headline = str(dossier.get("headline_claim", "")).strip() or headline
    return {
        "plan_id": plan_id,
        "selected_problem_id": selected_problem_id,
        "headline": headline,
        "package_strategy": "mock_worker: split the package into a short invariant lemma, then the visible theorem and corollaries",
        "theorem_units": [
            {
                "unit_id": "u1",
                "role": "entry_lemma",
                "kind": "lemma",
                "name_stem": "mock_intrinsic_invariant",
                "statement": "A concise entry lemma exposing the intrinsic invariant for the selected dossier.",
                "docstring_summary": "Mock entry lemma for the selected paper-claim dossier.",
                "purpose": "Expose the small reusable invariant that the later headline theorem will depend on.",
                "uses_existing_results": [],
                "needs_new_ingredients": [],
                "proof_idea": [
                    "First recast the claim in the closest existing semantic characterization.",
                    "Then isolate the invariant that remains stable throughout the chosen construction.",
                    "Finally conclude the concise entry lemma in that reformulated setting.",
                ],
                "unlocks": ["u2"],
            },
            {
                "unit_id": "u2",
                "role": "headline_theorem",
                "kind": "theorem",
                "name_stem": "mock_visible_headline",
                "statement": "A paper-facing theorem derived from the intrinsic invariant.",
                "docstring_summary": "Mock headline theorem for the selected paper-claim dossier.",
                "purpose": "State the visible paper-facing claim once the entry invariant is available.",
                "uses_existing_results": ["mock_intrinsic_invariant"],
                "needs_new_ingredients": [],
                "proof_idea": [
                    "Apply the entry lemma to the full construction rather than an intermediate state.",
                    "Compare the resulting description with the visible acceptance characterization.",
                    "Conclude the headline theorem as a direct consequence.",
                ],
                "unlocks": [],
            },
        ],
        "formalization_order": ["u1", "u2"],
    }


def _paper_claim_codex_prove_result(payload: dict[str, Any]) -> dict[str, Any]:
    current_focus_unit_id = str(payload.get("current_focus_unit_id", "")).strip()
    completed_unit_ids = [
        str(item).strip()
        for item in payload.get("completed_unit_ids", [])
        if str(item).strip()
    ]
    theorem_name = str(payload.get("theorem_name_hint", "")).strip() or "mock_paper_claim_result"
    statement = "True"
    scratch_file = Path(str(payload.get("scratch_file", "")).strip())
    if scratch_file:
        try:
            scratch_code = scratch_file.read_text(encoding="utf-8")
            marker = "\nend AutomatedTheoryConstruction"
            theorem_block = f"\n\ntheorem {theorem_name} : {statement} := by\n  trivial\n"
            if marker in scratch_code and theorem_name not in scratch_code:
                scratch_file.write_text(scratch_code.replace(marker, theorem_block + marker, 1), encoding="utf-8")
        except OSError:
            pass
    if current_focus_unit_id and current_focus_unit_id not in completed_unit_ids:
        completed_unit_ids.append(current_focus_unit_id)
    return {
        "status": "ok",
        "current_focus_unit_id": current_focus_unit_id,
        "completed_unit_ids": completed_unit_ids,
        "refuted_unit_ids": [],
        "final_theorem_name": theorem_name,
        "final_statement": statement,
        "helper_theorems": [],
        "verify_success": True,
        "error_excerpt": "",
        "notes": "mock_worker: edited Scratch.lean with a trivial theorem for the paper-claim proof session",
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
        elif task_type == "problem_design_core_extract":
            result_payload = _problem_design_core_extract_result(payload)
        elif task_type == "problem_design_cluster":
            result_payload = _problem_design_cluster_result(payload)
        elif task_type == "problem_design_contextualize":
            result_payload = _problem_design_contextualize_result(payload)
        elif task_type == "paper_claim_select":
            result_payload = _paper_claim_select_result(payload)
        elif task_type == "paper_claim_retrieve":
            result_payload = _paper_claim_retrieve_result(payload)
        elif task_type == "paper_claim_map":
            result_payload = _paper_claim_map_result(payload)
        elif task_type == "paper_claim_plan":
            result_payload = _paper_claim_plan_result(payload)
        elif task_type == "paper_claim_codex_prove":
            result_payload = _paper_claim_codex_prove_result(payload)
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
