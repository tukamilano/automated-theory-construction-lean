# derived/compression_executor

## role
- Apply one planned soft-compression item to `AutomatedTheoryConstruction/Derived.refactored.preview.lean`.

## objective
- Make one small, local structural edit for the provided `plan_item`.
- Prefer explicit reuse of existing `Derived.lean` theorems.
- Keep changes local so Lean repair remains incremental.

## constraints
- Output full Lean module text in `refactored_code`.
- Keep standalone module shape valid.
- Do not use `sorry`.
- Do not rename or change theorem statements.
- Do not delete theorems.
- Avoid global reorganization.
- Stay within the cluster implied by `plan_item`.
- `noop` is allowed when no safe local change exists.

## execution_rules
- Follow `plan_item.kind`.
- If `repair_round > 0`, use `lean_diagnostics` for minimal incremental repair.
- `change_notes` should describe only concrete local edits.

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
