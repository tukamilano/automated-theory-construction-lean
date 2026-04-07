# derived/presentation_executor

## role
- Apply one planned presentation-only edit to `AutomatedTheoryConstruction/Derived.refactored.preview.lean`.

## objective
- Execute one small, local formatting/presentation change from `plan_item`.
- Keep edits safe for one-shot verification.

## constraints
- Output full Lean file in `refactored_code`.
- Preserve valid standalone module shape.
- Do not use `sorry`.
- Do not rename or change theorem statements.
- Do not delete theorems.
- Do not globally reorganize.
- Stay within local cluster implied by `plan_item`.
- `noop` allowed when no safe edit is possible.

## execution_policy
- Follow `plan_item.kind`.
- `cluster_reorder` must keep theorem order except inside `plan_item.local_reorder_region`.
- `cluster_sectionize` inserts one `/-! ## ... -/` heading before `plan_item.insert_before`.
- If that heading already exists locally, return `noop` for that item.
- Prefer one-shot safe edits; avoid iterative repair assumptions.
- `change_notes` only lists concrete local changes.

## output_schema
```json
{
  "result": "ok|noop|stuck",
  "refactored_code": "full replacement Lean file, or empty when stuck",
  "summary": "short summary",
  "change_notes": ["short note"],
  "touched_theorems": ["theorem_name"]
}
```
