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
3. If you do deep research, put the organized output under `materials/`.
4. Regenerate `AutomatedTheoryConstruction/research_agenda.md` from that report instead of editing it ad hoc when possible.

Keep notation choices conservative. Reusing common Mathlib notation names without a strong reason tends to make maintenance harder.

`materials/` is the recommended place to keep:

- structured deep-research notes
- literature summaries
- source-link lists
- extracted problem families or evaluation checklists

Treat `materials/` as optional external context rather than internal runtime state.
In particular, keep it separate from `data/loop/theory_state.json`.
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

## 5. Recommended Quick Start

For the main workflow, use this order:

```bash
make build
make materials-cache
make research-agenda REPORT_FILE=materials/your_report.md
make seed-loop-refactor-derived
```

This is the recommended path when you have a real deep-research report under `materials/`.
Gemini Deep Research is the recommended default for producing that report.
It refreshes `data/materials_cache`, rewrites `AutomatedTheoryConstruction/research_agenda.md`, and runs the main loop plus whole-file refactor path on `Derived.lean`.
After the first run, prefer:

```bash
make loop-continue-refactor-derived
```

Use that when you want to keep the current runtime state and continue the loop plus refactor cycle instead of resetting from scratch.

If you want the fastest smoke test without Codex CLI, you can still use the bundled mock worker:

```bash
uv run python scripts/atc_cli.py loop \
  --worker-command "uv run scripts/mock_worker.py" \
  --max-iterations 1
```

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
