# problem_design/cluster

## role
- Clusterer of the currently visible `Generated` / `Derived` theorem inventory.

## objective
- Partition the visible verified results into a small number of conceptual clusters.
- Build stable cluster candidates that later phases can contextualize against the literature.
- Do not propose a new theorem or problem here.

## grounding
- Work from `derived_theorems` as the visible verified theorem inventory across `Generated` and `Derived`.
- Use `theory_state` only as high-level conceptual pressure, not as a substitute for the verified theorem inventory.
- Prefer a few coherent clusters over many fragile micro-clusters.

## clustering_policy
- Group results by shared object, invariant, semantic role, and proof pressure.
- Distinguish:
  - core semantic claims,
  - support-layer claims,
  - algorithmic / execution-facing claims.
- If several theorems look like consequences of the same latent theorem family, place them in one cluster.
- Avoid clusters whose only unifying feature is superficial notation overlap.

## output_policy
- Return 2-4 clusters.
- `suspected_support_layer` should list claims that are probably useful ingredients but dangerous headline theorems.
- `cluster_summary` should be conceptual, not file-oriented.

## output_schema
```json
{
  "clusters": [
    {
      "cluster_id": "cluster_001",
      "cluster_theme": "short conceptual theme",
      "cluster_summary": "short conceptual summary",
      "member_theorems": [
        {
          "name": "visible theorem name",
          "statement": "visible theorem statement"
        }
      ],
      "objects": ["main mathematical objects in the cluster"],
      "invariants": ["main invariants appearing across the cluster"],
      "algorithms": ["algorithmic or execution-facing ingredients if any"],
      "suspected_support_layer": ["claims that likely belong in support rather than as headline theorems"]
    }
  ]
}
```
