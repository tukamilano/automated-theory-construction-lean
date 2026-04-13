# Getting Started

This is the recommended first read after the root [`README.md`](../README.md).
Its job is narrow: get the repository building, point you at the first files to edit, and show the shortest path to a first successful run.

## 1. Prerequisites

Install or prepare:

- Lean toolchain from `lean-toolchain`
- Lake + Mathlib dependencies
- Python
- `uv`

Then bootstrap the repository:

```bash
make build
```

If you plan to use the real Codex-backed worker, also make sure Codex CLI works in this repository.
If you want Lean-aware agent tooling, enable `lean-lsp-mcp` in the environment where you run the worker.

## 2. Know The Main Files

Start with these paths:

- `AutomatedTheoryConstruction/Theory.lean`
- `AutomatedTheoryConstruction/Theory/Core.lean`
- `AutomatedTheoryConstruction/research_agenda.md`
- `materials/` if you want to keep reusable literature context alongside the theory

Keep `AutomatedTheoryConstruction/Theory.lean` as the public entry point for your active theory.
If you split the theory across multiple files under `AutomatedTheoryConstruction/Theory/`, add the corresponding `import` lines there.
When one file imports multiple local theory files, be careful not to create circular dependencies or to rely on transitive imports accidentally.
Keep the dependency direction intentional, and re-check both the edited file and `AutomatedTheoryConstruction/Theory.lean` after changing imports.

## 3. Make Your First Edits

The usual first changes are:

1. Put your base theory definitions and axioms in `AutomatedTheoryConstruction/Theory/Core.lean`.
2. Add helper lemmas or additional modules under `AutomatedTheoryConstruction/Theory/` if needed.
3. Edit `AutomatedTheoryConstruction/research_agenda.md` to state what kinds of problems the loop should value.
4. If you do deep research, put the organized output under `materials/`.

Keep notation choices conservative. Reusing common Mathlib notation names without a strong reason tends to make maintenance harder.

`materials/` is the recommended place to keep:

- structured deep-research notes
- literature summaries
- source-link lists
- extracted problem families or evaluation checklists

Treat `materials/` as optional external context rather than internal runtime state.
In particular, keep it separate from `data/theory_state.json`.
If a deep-research summary becomes old, keep using it as context, but treat its claims as lower-confidence than direct source links or primary papers.

## 4. Check The Lean Targets

After your first edits, verify the repository still checks:

```bash
make build
make check
```

If you only want to check the temporary verification target:

```bash
make check-scratch
```

## 5. Run A First Iteration

The fastest path is to use the bundled example theory with the mock worker:

```bash
uv run python scripts/atc_cli.py loop \
  --worker-command "uv run scripts/mock_worker.py" \
  --max-iterations 1
```

This verifies that the runtime loop works without requiring Codex CLI.

## 6. Seed Generation

`AutomatedTheoryConstruction/research_agenda.md` acts as the persistent value function for seed generation, prioritization, and expansion.
Keep it short and concrete. The default template covers themes, valued problem types, anti-goals, canonical targets, and soft constraints.

If you have domain-specific deep research, prefer storing it in `materials/` in an organized form rather than scattering it across ad hoc notes.
The runtime treats those files as optional external anchors for outward-looking generation and evaluation.
This is intentionally fail-soft: readable material can be used, and unreadable or partial material should only lower confidence rather than block the run.
The same applies to freshness: older summary reports can still be useful, but novelty-sensitive judgments should defer to source-link lists and the underlying papers.

Generate seeds from the current theory:

```bash
uv run python scripts/atc_cli.py seed \
  --seed-count 4
```

You can attach one-off extra context files when needed:

```bash
uv run python scripts/atc_cli.py seed \
  --context-file path/to/context.pdf \
  --seed-count 4
```

## Next Reads

- Operational workflows: [`USER_GUIDE.md`](USER_GUIDE.md)
- Ownership and safe edit boundaries: [`REPO_MAP.md`](REPO_MAP.md)
- Full doc index: [`README.md`](README.md)
