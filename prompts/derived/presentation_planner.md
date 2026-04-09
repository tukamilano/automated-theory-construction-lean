# derived/presentation_planner

## role
- Plan small, presentation-only edits for `AutomatedTheoryConstruction/Derived.refactored.preview.lean`.

## objective
- Improve local readability/structure without changing theorem inventory.

## constraints
<!-- INCLUDE: ../shared/derived_local_edit_constraints.md -->
- No proof-search rewrites.
- Each item must be local to one cluster.
- Return at most 5 items.
- `noop` is valid if no safe item exists.

## allowed_kinds
- `cluster_sectionize`
- `cluster_reorder`

## planning_policy
- Prefer `cluster_sectionize`.
- `cluster_sectionize` requires at least 2 related theorems and inserts only a `/-! ## ... -/` heading comment.
- Do not add sectionize if an equivalent local heading already exists.
- `cluster_reorder` must stay within a local region and only reorder when readability materially improves.

## output_schema
```json
{
  "result": "ok|noop|stuck",
  "summary": "short summary",
  "items": [
    {
      "id": "item_001",
      "kind": "cluster_sectionize|cluster_reorder",
      "anchor_theorems": ["theorem_name"],
      "rewrite_targets": ["theorem_name"],
      "new_theorems": ["optional_new_theorem_name"],
      "local_reorder_region": ["theorem_name"],
      "section_title": "optional short heading for cluster_sectionize",
      "section_members": ["theorem_name"],
      "insert_before": "optional theorem_name for cluster_sectionize",
      "expected_benefit": "short reason"
    }
  ]
}
```
