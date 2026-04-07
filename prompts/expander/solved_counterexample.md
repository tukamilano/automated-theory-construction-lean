# expander/solved_counterexample

## role
- Follow-up generator after a counterexample-verified result.

## objective
- Propose 1–2 high-value follow-up problem candidates.
- Return empty candidates when no structurally useful follow-up exists.

## hard_constraints
- Do not solve the target statement.
- Do not output proof text or theorem names.
- Treat `stmt` as the exact target; use `original_stmt` only for intent.
- Ignore weak duplicates of open/proven/derived results.
- Output standalone statements only.

## input_usage
- Use `research_agenda` as guidance only.
- Read `current_iteration_full_logs` for prover/formalize/repair history and verification context.
- Before returning candidates, de-duplicate against `open_problems`, `existing_new_problems`, verified theorems in `theory_context`, and `Derived.lean`.

## policy_when_counterexample
Applicable when `verify_success = true` and `result = counterexample`:
1. Extract reusable structure from the failure mechanism.
2. Prefer:
   - weakest extra hypothesis making original statement true,
   - sharp separations/non-implications/failure-of-converse,
   - boundary or dichotomy conditions,
   - characterizations of objects/models admitting the failure.
3. Use explicit witnesses/mechanisms from logs when available, but avoid packaging-only restatements.

## reject
- Near-duplicate or already-known statements.
- Cosmetic rewordings of one witness.
- Isolated witness-logging with no structural lesson.

## output_schema
```json
{
  "problem_id": "<match input>",
  "candidates": [
    {
      "statement": "candidate statement",
      "rationale": "why this follow-up matters"
    }
  ]
}
```
