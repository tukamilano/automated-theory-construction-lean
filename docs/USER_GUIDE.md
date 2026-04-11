# User Guide

This page collects the user-facing operational details that do not need to live in the root README.

For the initial setup order, see [`GETTING_STARTED.md`](GETTING_STARTED.md).

## Start Here

If you are new to this repository, begin with these paths:

- `AutomatedTheoryConstruction/Theory.lean`
- `AutomatedTheoryConstruction/Theory/*.lean`
- `AutomatedTheoryConstruction/research_agenda.md`

If you want the ownership map for generated files and advanced paths, see [`REPO_MAP.md`](REPO_MAP.md).

## What To Edit

To switch from the bundled example to your own theory, edit:

- `AutomatedTheoryConstruction/Theory.lean`
- `AutomatedTheoryConstruction/Theory/*.lean` as needed for local theory submodules
- `AutomatedTheoryConstruction/research_agenda.md` to define what kinds of problems are worth generating
- `AutomatedTheoryConstruction/seeds.jsonl` if you want to provide your own initial problems

`Theory.lean` remains the public entry point. If your theory grows beyond one file, keep the imports there and move detailed definitions or helper lemmas under `AutomatedTheoryConstruction/Theory/`.
If you split your theory across multiple files under `AutomatedTheoryConstruction/Theory/`, add the corresponding `import` lines to `AutomatedTheoryConstruction/Theory.lean`.

`AutomatedTheoryConstruction/research_agenda.md` is the persistent external value function. Seed generation, open-problem prioritization, and problem expansion read it automatically.
Optional extra reference files can still be passed ad hoc with `--context-file`.

## Swap the Proof Engine (without touching planning logic)

The loop treats planning/reasoning (`prover`, `formalizer`, `repair`) and Lean verification (`Scratch.lean` check) as separate concerns.
You can replace only the verification engine used for `Scratch.lean` checks.

- Set `ATC_PROOF_EXECUTOR` to a CLI command before running `atc_cli`.
- Keep prover/formalize/repair worker commands unchanged.
- Export contract-compatible JSON from the external process.

For complete schema and replacement steps, follow [`PROOF_EXECUTOR.md`](PROOF_EXECUTOR.md).

## Quick Mental Model

```text
[Theory.lean (+ optional Theory/*.lean)] + [AutomatedTheoryConstruction/research_agenda.md]
        ↓
[scripts/generate_seeds_from_theory.py]
  generate initial open problems
        ↓
[seeds.jsonl]
        ↓
+-------------------------------------------+
| [Theory.lean]                             |
|   entry module for base theory            |
|   + optional local theory submodules      |
|         ↓                                 |
| [scripts/run_loop.py]                     |
|   generate / formalize / prove / repair   |
|         ↓                                 |
| [Scratch.lean]                            |
|   temporary Lean verification             |
|         ↓                                 |
| [Derived.lean]                            |
|   accumulated verified theorems           |
+-------------------------------------------+
        ↓
[Derived.refactored.preview.lean]
  copy of Derived.lean used for review-time refactors
        ↓
[Derived.refactored.preview.lean]
        ↓
[scripts/apply_try_at_each_step_rewrites.py]
  direct proof-shortening rewrites from `tryAtEachStep`
        ↓
[Derived.refactored.preview.lean]
        ↓
[scripts/direct_refactor_derived.py]
  review-focused non-semantic cleanup
        ↓
[Derived.refactored.reviewed.lean]
```

## Refactor Design

The recommended refactor design is:

```text
pass 1.5
  whole-file rewrite cleanup
        ↓
pass 2.0
  whole-file review-focused cleanup
        ↓
split into Generated/C000x_*.lean
        ↓
per-file validation after split
        ↓
lake build AutomatedTheoryConstruction.Generated.Manifest
and repair at the whole-Generated level if needed
```

The key idea is that pass 1.5 and pass 2.0 are global stabilization passes, while generated-file splitting is used to make local validation and edits tractable.

`scripts/atc_cli.py materialize-generated` is the entrypoint for the split-based stage. It materializes `Generated/C000x_*.lean`, rebuilds `Manifest.lean` / `catalog.json`, and then performs generated-file verification and optional generated-level repair.

## Common Commands

The unified operational entrypoint is:

```bash
uv run python scripts/atc_cli.py --help
```

Config files are also supported:

```bash
uv run python scripts/atc_cli.py config show
```

If `atc.json` exists at the repo root, `scripts/atc_cli.py` picks it up automatically.

Build:

```bash
make build
```

Check the three main Lean targets:

```bash
make check
```

Regenerate seeds from the current theory:

```bash
uv run python scripts/atc_cli.py seed \
  --seed-count 4
```

Run the worker loop:

```bash
uv run python scripts/atc_cli.py loop
```

If you want to keep the current runtime state instead of reinitializing it:

```bash
make loop-continue
```

Run the one-shot pipeline from seed generation through refactor:

```bash
uv run python scripts/atc_cli.py pipeline \
  --max-iterations 40
```

Run the final refactor stages of `Derived.lean`:

```bash
cp AutomatedTheoryConstruction/Derived.lean AutomatedTheoryConstruction/Derived.refactored.preview.lean
uv run python scripts/atc_cli.py rewrite
uv run python scripts/atc_cli.py review
```

Run the split-based Generated materialization stage:

```bash
uv run python scripts/atc_cli.py materialize-generated
```

This stage prints progress directly to stderr while materializing generated chunks and rebuilding the manifest.

Equivalent `Makefile` shortcuts remain available:

```bash
make seed SEED_ARGS="--seed-count 4"
make loop LOOP_ARGS="--max-iterations 40"
make pipeline PIPELINE_ARGS="--max-iterations 40"
make rewrite
make review
```

## Codex Worker

If you have Codex CLI available and want the actual worker-backed loop:

```bash
uv run python scripts/atc_cli.py loop \
  --worker-command "uv run scripts/codex_worker.py" \
  --worker-timeout 420 \
  --codex-timeout 390 \
  --main-theorem-interval 10 \
  --main-theorem-formalize-worker-timeout 900 \
  --main-theorem-repair-worker-timeout 600
```

## More Detail

For low-level runtime behavior and implementation-oriented design notes, see [`../design/RUNTIME.md`](../design/RUNTIME.md).
