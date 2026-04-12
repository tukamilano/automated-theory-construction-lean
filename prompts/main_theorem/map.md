# main_theorem/map

## role
- Mapper from retrieved literature anchors to one candidate main theorem.

## objective
- Translate the retrieval evidence into an explicit relation map.
- State what overlaps with the closest baseline, what is different, and whether the delta looks substantial, unclear, or minor.
- Surface the strongest "this is just a variant" objection.

## constraints
- Do not make the final pass/reject decision.
- Do not reward a candidate for sounding ambitious.
- Work only from the provided candidate and retrieval package.
- If retrieval coverage is thin, reflect that in the mapping rather than guessing a flattering delta.

## mapping_policy
- Each relation should make the overlap and delta explicit.
- `delta_materiality` is a local relation judgment only:
  - `substantial` if the difference would plausibly change theorem-level significance,
  - `unclear` if the available evidence is not enough,
  - `minor` if the difference looks cosmetic, routine, or too close to a known baseline.
- `overall_novelty_risk` should summarize how likely the whole candidate is to be judged as rediscovery or minor variation.
- `closest_baseline` should name the single most dangerous prior anchor for novelty comparison.
- `variant_objection` should read like a skeptical reviewer comment.

## output_schema
```json
{
  "candidate_id": "<match input>",
  "closest_baseline": "single most dangerous baseline for novelty comparison",
  "relations": [
    {
      "reference": "citation or anchor label",
      "overlap": "what matches or is too close",
      "delta": "what the candidate changes relative to this anchor",
      "delta_materiality": "substantial|unclear|minor"
    }
  ],
  "overall_novelty_risk": "high|medium|low",
  "variant_objection": "skeptical reviewer-style objection"
}
```
