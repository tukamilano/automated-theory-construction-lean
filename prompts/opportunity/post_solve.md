# opportunity/post_solve

## role
- Detect at most one unusually strong follow-up opportunity after a solve event.
- This is not a primary problem generator.

## objective
- Return one opportunity only when the solve event exposes a strong bridge, boundary, criterion, or obstruction with clear frontier value.
- Otherwise return `opportunity: null`.

## inputs
- `source_kind`: `open_problem|main_theorem`
- `solve_result`: `proof|counterexample|stuck`
- `theory_state`
- visible theory, queue context, and recent logs

## non_goals
- Do not generate multiple candidates.
- Do not produce routine local continuations.
- Do not assume the opportunity should be added to the queue immediately.
- Do not reward local naturalness alone.

## admission_rule
Return an opportunity only if at least one of the following holds:
- the solved result exposes a new bridge between previously separate parts of the theory,
- it makes a converse / non-converse / criterion / sharp boundary suddenly concrete,
- it directly unlocks a listed bottleneck or missing bridge in `theory_state`,
- it suggests a locally scoped but sharp lemma that isolates a real obstruction, threshold, criterion, or reusable reduction step exposed by the solve event,
- it reveals a reusable obstruction or failure mechanism with clear general value.

## rejection_rule
Return `opportunity: null` if the best follow-up is:
- a nearby corollary,
- a local support lemma without sharp content or clear bottleneck-relief value,
- a minor assumption variation,
- a continuation inside an overexplored pattern,
- or a statement with weak summary-level effect.

## statement_style
- If returning an `opportunity.statement`, write it in repository Lean style.
- Prefer existing notation and abbreviations over expanded names when available.
- For example, prefer `x ≐ y` over `ACR.Equivalent x y`, and `⊠x` over `ACR.Reft.reft x`.
- Avoid unnecessarily fully-qualified operator paths unless required to disambiguate parsing.

## output_schema
Return exactly this JSON object only:
```json
{
  "source_id": "<match input>",
  "opportunity": {
    "statement": "candidate statement",
    "kind": "bridge|boundary|criterion|obstruction",
    "unlocks": "what frontier item this could unlock",
    "why_now": "why this became visible only after the solve event",
    "why_not_peripheral": "why this is not merely a nearby extension"
  }
}
```

If no strong opportunity exists, return:
```json
{
  "source_id": "<match input>",
  "opportunity": null
}
```
