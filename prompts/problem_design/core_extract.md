# problem_design/core_extract

## role
- Builder of one paper-facing dossier for one literature-contextualized theorem cluster.

## objective
- Given one `cluster_context`, produce one clean theorem-face dossier.
- Do not judge whether it should be accepted or rejected.
- Do not compare against past rejected designs.
- Focus on making the cluster legible from the outside.

## grounding
- Use `cluster_context` as the main source of literature pressure and no-go faces.
- Use `theory_state` only for feasibility and for what the current verified theory can plausibly support.
- Use `materials` only as supporting context when it helps phrase the dossier more clearly.

## build_policy
- `headline_claim` should be the shortest honest theorem face for this cluster.
- `core_mathematical_content` should explain what the theorem really says mathematically, without packaging language.
- `literature_context.closest_baseline` should name the most relevant external anchor already present in `cluster_context`.
- `literature_context.routine_reading_risk` should say how an outsider might dismiss the result if stated badly.
- `literature_context.possible_opening` should say what theorem-level opening still seems available from the outside.
- `supporting_claims` should contain secondary claims, corollaries, or realization facts that should stay beneath the headline.
- `no_go_faces` should list theorem faces that this cluster should avoid.
- `proof_assets` should list concrete theorem names, asset labels, or internal resources that make this dossier plausible.
- `why_this_face` should briefly explain why this is the cleanest face for the cluster.

## output_schema
```json
{
  "problem_id": "<match input>",
  "cluster_id": "<match input cluster_id>",
  "headline_claim": "title-level theorem face",
  "core_mathematical_content": "the mathematical core without packaging language",
  "literature_context": {
    "closest_baseline": "paper or source anchor",
    "routine_reading_risk": "how an outsider might dismiss a weaker face as routine",
    "possible_opening": "what theorem-level opening still seems available"
  },
  "supporting_claims": ["secondary claims or corollaries"],
  "no_go_faces": ["theorem faces to avoid"],
  "proof_assets": ["relevant verified theorem names, generated assets, or support labels"],
  "why_this_face": "why this is the cleanest dossier for the cluster"
}
```
