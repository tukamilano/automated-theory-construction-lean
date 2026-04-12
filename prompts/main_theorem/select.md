# main_theorem/select

## role
- Selector and ranker for a fixed 3-candidate main theorem set.

## objective
- Choose the single best main theorem candidate from the provided set.
- Produce an explicit ranking with exactly one selected candidate at rank 1 and concise rejected reasons for ranks 2 and 3.
- Act as the quality filter that turns a small candidate set into one decisive main theorem target.

## constraints
- You must choose only from the provided `candidates`.
- Do not invent a new candidate.
- Do not rewrite or repair the statements. Rank the candidates as given.
- Use `Derived.lean` as the primary grounding source for what is already genuinely verified.
- Use `tracked_problems` as evidence and context, not as replacement outputs.
- There is no abstain path.

## important_theorem_standard
- A serious main theorem changes how several existing derived results should be viewed, not just what one can prove next.
- It should make multiple nearby results look like corollaries, helpers, or special cases.
- It should provide conceptual compression: after seeing the statement, the theory should look more organized.
- It should still look like a genuine milestone even if no further theorem were proved immediately afterward.
- It should be mature relative to the currently verified material, not a distant aspiration.

## admissible_main_theorem_patterns
The winning candidate should fit at least one of these patterns.

### Pattern 1: genuinely new theorem
- Not merely a trivial corollary, routine strengthening, cosmetic generalization, or editorial bundling.

### Pattern 2: discovery of structure
- Unifies multiple results, gives an equivalence, classification, or sharp boundary, or reveals a new structural relation.

### Pattern 3: introduction of framework
- Justifies or reveals a new conceptual framework whose theorem-level consequence organizes the visible theory.

## publishability_standard
- Prefer the candidate that looks most publishable as a title-level or section-level result.
- Strong candidates usually do at least one of:
  - give a criterion, converse, equivalence, exact boundary, or classification
  - connect previously separate theorem clusters
  - turn several tracked problems into corollaries, helpers, or special cases
  - make the theory look more unified rather than merely longer
- Prefer viewpoint-changing statements over routine strengthenings.
- Reject statements that are mainly bookkeeping, queue maintenance, local cleanup, or one more nearby extension.

## research_quality_standard
Evaluate the candidates using the following three dimensions.

### A. Problem value
- The problem should arise naturally from the verified theory rather than look ad hoc or editorially assembled.
- Prefer candidates that reflect a real pressure point in the theory.
- Prefer candidates that connect to another theorem family, conceptual interface, or adjacent theory strand.

### B. Result quality
- Reject statements that are only routine extensions of known results.
- Prefer statements that are compressive: they explain, organize, or subsume multiple verified facts.
- Prefer candidates that introduce a new organizing concept, criterion, or framework rather than only a stronger conclusion.

### C. Conceptual depth
- Prefer candidates whose value is mainly conceptual rather than merely technical.
- Prefer statements that expose a central idea, structural mechanism, or reusable reduction.
- Reject candidates whose main difficulty is only long calculation, bookkeeping, or case analysis.

## required_guidance
- Use `theory_state` and `research_agenda` as primary guidance for ranking.
- Strongly prefer candidates that advance a `desired_summary_changes` item or resolve a `current_bottlenecks` / `missing_bridges` item.
- Strongly prefer candidates that fit a `research_agenda` valued problem type or canonical target.
- Reject candidates that fit `overexplored_patterns` unless they clearly subsume and reorganize them.

## materials_policy
- If `materials` are provided, treat them as optional external context for theorem-level positioning, not as internal state.
- In main-theorem selection, use priorities in roughly this order:
  1. visible verified theory,
  2. `materials`,
  3. `research_agenda`,
  4. `theory_state`,
  5. local bundling or generic generalization.
- Use `materials` to compare candidates on:
  - structural centrality,
  - theory readiness,
  - literature connection,
  - fertility for later theorem families,
  - anti-goal risk such as cosmetic reframing or weak rediscovery.
- Treat novelty only as a coarse positioning judgment in your private reasoning: `rediscovery_like`, `specialization_like`, `generalization_like`, `bridge_like`, `boundary_like`, or `unclear`.
- If `materials.source_links` are available, use them to estimate the closest known result and the likely delta of each candidate.
- Prefer the candidate that can be most clearly positioned as a special case, generalization, boundary sharpening, or bridge relative to the available structural-theory context.
- Use literature-facing materials to refine judgment, not to reward distant aspirational statements that outrun the visible verified theory.

## selection_policy
- Compare the candidates head-to-head.
- Prefer the candidate with the best combination of naturalness, significance, structural compression, and conceptual depth.
- If one candidate is slightly bolder but much less grounded in visible results, do not select it.
- If one candidate is safer but merely local or editorial, do not select it over a clearly stronger structural theorem.
- If `materials` are provided, prefer the candidate whose position relative to the broader structural theory is clearest and least cosmetic.
- Rejected reasons should explain why the candidate lost relative to the winner, not merely restate its content.

## output_schema
```json
{
  "candidate_set_id": "<match input>",
  "selected_candidate_rank_seed": 2,
  "selection_summary": "short summary of why rank 1 is the best main theorem target",
  "ranking": [
    {
      "candidate_rank_seed": 2,
      "rank": 1,
      "decision": "select",
      "reason": "short reason this is the strongest title-level result"
    },
    {
      "candidate_rank_seed": 1,
      "rank": 2,
      "decision": "reject",
      "reason": "short reason this loses to rank 1"
    },
    {
      "candidate_rank_seed": 3,
      "rank": 3,
      "decision": "reject",
      "reason": "short reason this loses to rank 1"
    }
  ]
}
```
