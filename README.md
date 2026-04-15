# Automated Theory Construction

Automated Theory Construction (ATC) is a Lean 4 workflow for building verified theory from a small axiom base.
Instead of aiming at one hand-picked theorem, the system generates candidate statements, formalizes them, verifies them in Lean, and accumulates successful results into a growing derived theory.

## Core Idea

> Do not aim directly at the final theorem. Generate the surrounding structure until the theorem becomes inevitable.

The main loop works like this:

1. Start from a base theory in `AutomatedTheoryConstruction/Theory.lean`.
2. Generate local candidate statements from the current theory state.
3. Attempt formalization and proof in Lean.
4. Append verified results to `AutomatedTheoryConstruction/Derived.lean`.
5. Recycle failed attempts into refined follow-up problems.

This is theory construction rather than ordinary proof search: the system expands the space of statements as it works.

## Quick Start

The recommended end-to-end path is:

1. Put your deep-research report under `materials/`. Gemini Deep Research is the recommended default for this step.
2. Build the materials cache.
3. Regenerate `AutomatedTheoryConstruction/research_agenda.md` from that report.
4. Run the main seed -> loop -> refactor pipeline.
5. Run a one-shot paper-claim session.

Prerequisites:

- Lean toolchain from `lean-toolchain`
- Lake + Mathlib dependencies
- Python
- `uv`

Run:

```bash
make build
make materials-cache
make research-agenda REPORT_FILE=materials/your_report.md
make seed-loop-refactor-derived
make paper-claim
```

This builds the project, refreshes `data/materials_cache`, writes `AutomatedTheoryConstruction/research_agenda.md`, runs the main loop plus whole-file refactor path on `Derived.lean`, and then runs a paper-claim session.

For subsequent iterations after the first `make seed-loop-refactor-derived`, prefer `make loop-continue-refactor-derived` so the loop/refactor cycle continues from the current runtime state instead of resetting it.
If you want to continue only the loop without the refactor stages, use `make loop-continue`.
If you only want to refresh derived `materials/` artifacts without fetch/extract, use `make materials-derive`.
If you want the fastest smoke path without Codex CLI, you can still run:

```bash
uv run python scripts/atc_cli.py loop \
  --worker-command "uv run scripts/mock_worker.py" \
  --max-iterations 1
```

## Documentation

Start with the doc hub: [`docs/README.md`](docs/README.md)

| If you want to... | Read |
| --- | --- |
| Set up the repo and do a first run | [`docs/GETTING_STARTED.md`](docs/GETTING_STARTED.md) |
| Run the loop day to day | [`docs/USER_GUIDE.md`](docs/USER_GUIDE.md) |
| Know what files are safe to edit | [`docs/REPO_MAP.md`](docs/REPO_MAP.md) |
| Swap the Lean verification backend | [`docs/PROOF_EXECUTOR.md`](docs/PROOF_EXECUTOR.md) |
| See implementation-oriented runtime notes | [`design/RUNTIME.md`](design/RUNTIME.md) |

## Repository Shape

- `AutomatedTheoryConstruction/Theory.lean`: entry point for the active base theory
- `AutomatedTheoryConstruction/Theory/*.lean`: optional local theory modules
- `AutomatedTheoryConstruction/Derived.lean`: accumulated verified theorems
- `AutomatedTheoryConstruction/Scratch.lean`: temporary verification target
- `AutomatedTheoryConstruction/research_agenda.md`: persistent guidance for problem selection
- `materials/`: recommended place to keep organized deep-research outputs, literature summaries, source-link lists, and problem-seed notes used as optional external context
- `prompts/research_agenda/`: templates for turning deep-research reports into strict `research_agenda.md` drafts
- `scripts/atc_cli.py`: unified operational CLI

`materials/` is the recommended home for deep research that you want the system to reuse later.
Treat it as external research context, not as part of the core runtime state: the loop may consult it for seed generation, prioritization, expansion, and paper-claim positioning, but it should not be folded into `theory_state.json`.
Also treat summary reports in `materials/` as potentially time-sensitive: they are useful for context, but source-link lists or primary papers should win when novelty or closest-known-result judgment matters.

To regenerate `AutomatedTheoryConstruction/research_agenda.md` from a deep-research report, use:

```bash
make research-agenda REPORT_FILE=materials/your_report.md
```

## Refactor Pipeline

The post-loop refactor path is intentionally staged:

1. Alpha-equivalent theorem dedupe on the preview copy
2. Whole-file rewrite cleanup (`rewrite`, pass 1.5)
3. Whole-file review-focused cleanup (`review`, pass 2.0)
4. Copy the reviewed result back into `Derived.lean`
5. Recheck the main Lean targets against the updated derived theory

This keeps global cleanup separate from proof search while still ending on a verified `Derived.lean`.

## License

This repository is licensed under the MIT License. See `LICENSE`.

## Acknowledgements

The prompting strategy for solving Lean problems was partially inspired by a private repository, `kmd710/lean4-codex-skills`.

This repository also includes material adapted from:

- <https://github.com/SnO2WMaN/provability-toy>
- <https://github.com/tani/mathling/tree/main>
