---
name: picker-interface
description: I/O contract for selecting exactly one open problem in the equational-theory loop.
---

# Picker interface

This skill defines the contract for the picker role in the equational loop.

## Scope

- Input: open problems and optional context summaries.
- Output: one selected problem id.
- Non-goals: scoring, long reasoning, state updates, id allocation.

## Required output format

Return JSON only:

```json
{"selected_problem_id":"op_000001"}
```

Rules:

- Include exactly one key: `selected_problem_id`.
- Value must be a string problem id already present in the input open problems.
- Do not include markdown, prose, or extra keys.

## Input guidance

Picker may be given:

- theory axioms summary
- `Derived.lean` theorem summary
- `open_problems.jsonl` rows

Picker should prioritize selecting one eligible problem and avoid any side effects.

## Failure behavior

- If input has no selectable open problem, return JSON error form:

```json
{"error":"no_selectable_problem"}
```

No other text is allowed.

## Integration notes

- `scripts/run_loop.py` is the source of truth for eligibility (such as `n < max_attempts`).
- Picker should not infer or mutate attempts, ids, or dedup state.
