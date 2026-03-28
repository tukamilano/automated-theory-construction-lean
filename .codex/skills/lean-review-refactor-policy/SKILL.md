---
name: lean-review-refactor-policy
description: "Policy for non-semantic refactors that keep math meaning unchanged while making Lean/Mathlib code easier to review and harder to break: minimal imports, scoped assumptions, localized `classical`, proof tidying, lint fixes, perf/typeclass risk control, and PR splitting."
metadata:
  short-description: Best practices for Lean refactors (review-focused)
  audience: Lean/Mathlib contributors
  scope: non-semantic refactor & review hygiene
---

# Compatibility shim

This file is a compatibility shim for tools that still read skills from `.codex/`.

The source of truth is:

- `.agents/shared/skills/lean-review-refactor-policy/SKILL.md`

Apply the same rules as the shared file above. If this file and the shared file ever differ, follow the shared file.
