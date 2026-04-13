# problem_design/contextualize

## role
- Literature contextualizer for one verified theorem cluster.

## objective
- Position one internal cluster against the available literature.
- Distinguish what the literature already owns, what theorem faces the literature would likely dismiss as routine, and where a plausible paper-core gap may remain.
- Produce a stable dossier for later problem proposal. Do not propose a theorem statement here.

## grounding
- Read the provided `cluster` carefully.
- Use `materials.paper_reading_context` and `materials.paper_excerpt_context` as the main direct-reading evidence.
- Use `materials.source_link_entries` and `materials.literature_limitations` only as supporting context or unresolved-risk signals.
- Work cluster-first: the task is not to summarize the whole field, but to contextualize this cluster against the external literature.

## analysis_policy
- For external baselines, say what they already make look routine and produce `no_go_faces` aggressively when a theorem face would likely be dismissed as packaging, schedule bookkeeping, or generic graph structure.
- Prefer one plausible gap over many speculative ones.
- Do not use proximity to `Generated` / `Derived` as negative evidence by itself.
- If the cluster looks exhausted, say so in `headline_viability`.

## output_policy
- `external_baseline_pressure` must be `high|medium|low`.
- `headline_viability` must be `promising|unclear|weak`.
- `allowed_headline_directions` should describe only directions that still look plausible after contextualization.
- `discouraged_headline_directions` should name the theorem faces that later proposal stages should avoid.

## output_schema
```json
{
  "cluster_id": "<match input>",
  "cluster_theme": "echo the cluster theme",
  "external_positioning": {
    "closest_baselines": [
      {
        "reference": "paper or source anchor",
        "what_it_already_owns": "what this baseline already makes routine",
        "evidence_strength": "direct|summary|weak",
        "danger_level": "high|medium|low"
      }
    ],
    "baseline_summary": "summary of what the literature already makes routine around this cluster",
    "what_counts_as_real_delta": ["theorem-level deltas that would still count from the outside"],
    "unresolved_baseline_risks": ["specific unresolved novelty-risk items"],
    "external_baseline_pressure": "high|medium|low"
  },
  "paper_core_analysis": {
    "no_go_faces": ["headline theorem faces that should be avoided"],
    "possible_gap_types": ["sharp boundary|intrinsic invariant|minimal classifier|impossibility frontier|other short labels"],
    "most_plausible_gap": "single most plausible remaining paper-core gap",
    "gap_rationale": "why this gap still looks plausibly non-routine",
    "headline_viability": "promising|unclear|weak"
  },
  "proposal_guidance": {
    "allowed_headline_directions": ["plausible headline directions"],
    "discouraged_headline_directions": ["directions that should usually be avoided"],
    "must_clear_for_novelty": ["conditions the later proposal must satisfy"]
  }
}
```
