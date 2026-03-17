---
name: prover-interface
description: I/O contract for proof/counterexample/stuck attempts and post-attempt new-problem proposals.
---

# Prover interface

This skill defines the contract for the prover role in the equational loop.

## Scope

- First attempt the given problem.
- Then optionally propose up to two new problems that emerged from that attempt.
- Non-goals: deterministic state transitions, id generation, JSONL updates, final dedup.

## Required output format

Return JSON only:

```json
{
  "problem_id": "op_000001",
  "result": "stuck",
  "proof_text": "",
  "counterexample_text": "",
  "new_problems": []
}
```

Rules:

- `problem_id`: must match input target problem id.
- `result`: exactly one of `proof`, `counterexample`, `stuck`.
- `proof_text`: string. Empty string is allowed.
- `counterexample_text`: string. Empty string is allowed.
- `new_problems`: array of strings, length 0-2.

## Behavioral constraints

- Attempt the original problem before proposing new problems.
- New problems must arise from the attempt itself.
- Avoid trivial variations (renaming-only, mirror-only, obvious duplicates).
- Prefer generalized, non-trivial variants over one-step axiom restatements.
- At least one suggested problem should have a meaningfully different shape from the current target.
- Do not exceed two new problems.

## Mathlib usage

- Mathlib lemmas/tactics are allowed in `proof_text` as long as output remains valid Lean tactic code.

## Dedup and state boundary

- Prover performs best-effort duplicate avoidance.
- Final duplicate filtering is deterministic and owned by `scripts/state_update.py`.
- Prover must not perform id allocation or state mutation.

## Formalization boundary

- If target statement is not formalizable to Lean, downstream formalization may reject it.
- Rejection handling is deterministic: keep problem in `open` and increment attempts.

## proof_text format requirement

- `proof_text` MUST contain Lean 4 tactic code only when `result` is `proof`.
- The content is inserted verbatim into a `by` block in a Lean theorem file.
- Do NOT put natural language, explanations, or comments in `proof_text`.
- Example of valid `proof_text`:
  ```
  intro α _ x
  exact SemigroupLike01.ax_left_idempotent x
  ```
- Example of INVALID `proof_text` (will cause Lean compile error):
  ```
  The statement follows from ax_left_idempotent.
  ```
