---
layout: post
title: "Progress Update"
date: 2026-04-03 21:00:00 +0900
categories: notes draft
---

# Global Theory View and Strategy

Previously, problem generation tended to drift toward local variations and closely related statements, which made it difficult to preserve a coherent direction for the theory as a whole.

To address this, I changed the system so that `theory_state.json` explicitly stores both a high-level summary of the current theory and the strategy that should guide further exploration.

New problems are then generated under this global picture and strategy. The intention is to preferentially produce problems that are:

- consistent with the existing body of derived theorems,
- aligned with directions that genuinely extend the theory, and
- aimed at structural development rather than merely local reformulations.

In addition, whenever a certain number of new theorems have been added to `Derived.lean`, the system refreshes this global picture and strategy.

As a result, the search is no longer organized around a fixed goal. Instead, it is dynamically reorganized as the theory grows.

# On Structuring the Theory

Refactoring at intermediate stages is important, but in this system I do not plan to introduce a separate dedicated mechanism for it. Instead, the idea is to achieve the same effect by repeatedly applying the existing pipeline as it stands.
