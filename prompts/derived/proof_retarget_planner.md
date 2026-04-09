# derived/proof_retarget_planner

## role
- Plan small proof-retarget edits in `AutomatedTheoryConstruction/Derived.refactored.preview.lean`.

## objective
- Identify local rewrites that make existing derived theorems explicitly reusable.
- Focus on direct rewrites where a theorem can be proved from shape-compatible support results.

## constraints
<!-- INCLUDE: ../shared/derived_local_edit_constraints.md -->
- Each item stays local to one theorem cluster.
- Return at most 5 items.
- `noop` is valid if no safe target exists.

## allowed_kind
- `proof_retarget`

## planning_policy
- Prefer items with low risk and clear dominance/subsumption structure.
- Prefer explicit reuse path over speculative proof reshaping.

## output_schema
```json
{
  "result": "ok|noop|stuck",
  "summary": "short summary",
  "items": [
    {
      "id": "item_001",
      "kind": "proof_retarget",
      "anchor_theorems": ["theorem_name"],
      "rewrite_targets": ["theorem_name"],
      "new_theorems": ["optional_new_theorem_name"],
      "expected_benefit": "short reason"
    }
  ]
}
```
