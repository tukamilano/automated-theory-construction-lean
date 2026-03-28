# Codex Compatibility Instructions

This file is a compatibility shim for tools that still look under `.codex/`.

The source of truth is:

- `.agents/shared/AGENTS.md`

Supporting shared guidance lives under:

- `.agents/shared/skills/**/SKILL.md`
- `.agents/shared/workflow/**`

Codex-specific rule:

- If your tool discovered this file through `.codex/`, apply the same policies as `.agents/shared/AGENTS.md`.
- If this file and `.agents/shared/AGENTS.md` ever differ, follow `.agents/shared/AGENTS.md`.
