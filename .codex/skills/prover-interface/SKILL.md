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
- Do not exceed two new problems.

## Dedup and state boundary

- Prover performs best-effort duplicate avoidance.
- Final duplicate filtering is deterministic and owned by `scripts/state_update.py`.
- Prover must not perform id allocation or state mutation.

## Formalization boundary

- If target statement is not formalizable to Lean, downstream formalization may reject it.
- Rejection handling is deterministic: keep problem in `open` and increment attempts.
