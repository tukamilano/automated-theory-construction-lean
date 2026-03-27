---
layout: post
title: "Progress Update"
date: 2026-03-27 21:00:00 +0900
categories: notes progress draft
---

# Main Loop Session and Search Policy for Automated Theory Construction

## Overview

*Note: This section documents newly introduced design considerations as part of ongoing progress in the system.*

The search loop in automated theory construction tends to exhibit a strong bias toward generating transformed statements derived from existing theorems, including generalizations and technical lemmas. While such statements are useful for extracting local properties of a theory, they do not necessarily contribute to a unified or compressed global structure.

To address this limitation, we introduce a *main-loop session* centered around identifying and proving structurally significant theorems ("main theorems"). This mechanism is designed to periodically reorganize and compress the accumulated theory.

---

## Main-Loop Session

The main-loop session operates as follows:

1. **Trigger Condition**
   Every time *N* new lemmas are added to `Derived.lean`, a main-theorem session is triggered.

2. **Candidate Suggestion**
   The system analyzes `Derived.lean` and uses `main_theorem_suggester.md` to propose at most one candidate for a main theorem.
   Strict filtering criteria are imposed, and proposing no candidate is explicitly allowed.

3. **Proof Planning**
   If a candidate is proposed, `main_theorem_planner.md` is used to construct a natural-language proof plan.

4. **Formalization Loop**
   Based on `.codex/agents.md` and `SKILL.md`, the system attempts to formalize the theorem in Lean.
   The loop continues until all `sorry` placeholders are eliminated.

5. **Post-Success Expansion**
   If formalization succeeds:

   * The theorem is appended to `Derived.lean`.
   * `post_theorem_expander.md` is invoked to generate five new open problems.

This process introduces periodic global restructuring pressure into the otherwise local search dynamics.

---

## Pick-Up Policy (Open Problem Prioritization)

To improve search efficiency, we introduce a prioritization scheme for open problems.

### Priority Levels

Each open problem is assigned one of three priority levels: `high`, `medium`, or `low`, determined by `open_problem_prioritizer.md`.

### Core Rubric

* `high`

  * Connects existing theorem clusters.
  * Gives a strong equivalence, characterization, or existence statement.
  * Looks likely to unlock many future problems or reorganize the theory.
* `medium`

  * A natural local extension or useful nearby consequence.
  * Likely to help only one or two nearby problems.
* `low`

  * Cosmetic variant, shallow restatement, obvious weakening, or low-utility statement in the current `Derived.lean` context.
  * Already looks effectively covered by current verified theorems up to a shallow reformulation.

### Additional Policies

* If an open problem fails twice, it is removed from the pool.
* Priorities are periodically refreshed:

  * After every *M* new additions.
  * After each successful main-loop formalization.

This prioritization ensures that computational resources are allocated toward structurally meaningful progress.

---

## Scope and Generality

To improve general applicability, we relax the requirement that the system must always start strictly from axioms. However, to avoid drift during exploration, we impose the requirement that a core Lean theory file defining the domain must always be present.

This balance allows:

* Controlled exploration within a defined domain.
* Flexibility in incorporating partially structured or pre-existing theories.

---

## Research Direction

The long-term objective of this framework is to:

* Enable systematic rediscovery and exploration of niche or underdeveloped domains.
* Revisit and restructure “mature” or seemingly exhausted areas of theory.
* Improve usability and accessibility of automated theory construction systems.

By combining local search with periodic global restructuring, the system aims to produce theories that are not only larger, but also more coherent and interpretable.

---

## Summary

The introduction of the main-loop session and prioritization policies transforms the search process from purely accumulative to structurally aware. Instead of merely growing `Derived.lean`, the system actively attempts to compress, reorganize, and elevate the theory through strategically selected main theorems.

