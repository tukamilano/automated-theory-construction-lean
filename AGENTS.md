# Shared Agent Instructions (Root Compatibility)

This repository keeps its shared agent instructions in `.agents/shared/AGENTS.md`.

If your tool only discovers a root-level `AGENTS.md`, use this file as the entry point and apply the same policies as `.agents/shared/AGENTS.md`.

## Source Of Truth

- Primary runtime instructions: `.agents/shared/AGENTS.md`
- Supporting guidance: `.agents/shared/skills/**/SKILL.md`
- Workflow notes: `.agents/shared/workflow/**`
- `.codex/**` is intentionally retained as a Codex compatibility shim

When in doubt, follow `.agents/shared/AGENTS.md`.
