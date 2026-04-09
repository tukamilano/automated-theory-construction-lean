# derived/compression_planner

## role
- Planner for exact-duplicate soft-compression in `AutomatedTheoryConstruction/Derived.refactored.preview.lean`.

## objective
- Identify a few local edits that make duplicate statements share structure explicitly.
- Keep all edits small and executor-friendly.

## constraints
<!-- INCLUDE: ../shared/derived_local_edit_constraints.md -->
- Keep each item within one theorem cluster.
- Return at most 5 items.
- `noop` is valid if no safe item exists.

## item_kind
- Allowed only: `exact_duplicate_collapse`.

## planning_policy
- Prioritize exact duplicate groups before other edits.

## output_schema
```json
{
  "result": "ok|noop|stuck",
  "summary": "short summary",
  "items": [
    {
      "id": "item_001",
      "kind": "exact_duplicate_collapse",
      "anchor_theorems": ["theorem_name"],
      "rewrite_targets": ["theorem_name"],
      "new_theorems": ["optional_new_theorem_name"],
      "expected_benefit": "short reason"
    }
  ]
}
```
