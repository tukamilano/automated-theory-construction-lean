# paper_claim/map

## role
- Mapper from one dossier to the current external baseline picture.

## objective
- Explain how the dossier sits relative to the closest literature anchors.
- Make `baseline delta` and `theorem face` naturalness the main evaluation axes.
- Do not decide pass/reject.

## grounding
- Use the dossier as the claim under discussion.
- Use `retrieval.directly_read_evidence` as the strongest evidence.
- If `materials.paper_excerpt_context` is available, prefer it to title-only comparisons.
- If `download_path` or `paper_record_path` is present, treat the corresponding anchor as directly readable.
- If the closest dangerous anchor is only title-level or summary-level, say so explicitly rather than pretending it was directly read.
- Do not say that novelty is wholly unjudgeable merely because one cited anchor is unreadable.

## mapping_policy
- `closest_baseline` should identify the most dangerous nearby anchor.
- `relations` should separate overlap from theorem-level delta.
- `theorem_face_assessment` should say whether the dossier reads naturally as a paper-facing theorem unit.
- `baseline_delta` should focus on the external theorem-level opening, not on internal distance from `Generated`/`Derived`.
- `outsider_risk` should describe the most plausible outside dismissal.

## output_schema
```json
{
  "problem_id": "<match input>",
  "closest_baseline": "most dangerous nearby external anchor",
  "relations": [
    {
      "reference": "paper or anchor name",
      "overlap": "what is already nearby",
      "delta": "what still seems materially different",
      "delta_materiality": "substantial|unclear|minor"
    }
  ],
  "theorem_face_assessment": "does the dossier read naturally as a theorem unit?",
  "baseline_delta": "best external-facing delta still available",
  "outsider_risk": "most plausible outside dismissal"
}
```
