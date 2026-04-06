# User Guide

This page collects the user-facing operational details that do not need to live in the root README.

For the initial setup order, see [`GETTING_STARTED.md`](GETTING_STARTED.md).

## Start Here

If you are new to this repository, begin with these paths:

- `AutomatedTheoryConstruction/Theory.lean`
- `AutomatedTheoryConstruction/Theory/*.lean`
- `materials/`

If you want the ownership map for generated files and advanced paths, see [`REPO_MAP.md`](REPO_MAP.md).

## What To Edit

To switch from the bundled example to your own theory, edit:

- `AutomatedTheoryConstruction/Theory.lean`
- `AutomatedTheoryConstruction/Theory/*.lean` as needed for local theory submodules
- `AutomatedTheoryConstruction/seeds.jsonl` if you want to provide your own initial problems

`Theory.lean` remains the public entry point. If your theory grows beyond one file, keep the imports there and move detailed definitions or helper lemmas under `AutomatedTheoryConstruction/Theory/`.
If you split your theory across multiple files under `AutomatedTheoryConstruction/Theory/`, add the corresponding `import` lines to `AutomatedTheoryConstruction/Theory.lean`.

For seed-generation context, put notes, drafts, papers, or problem sketches under `materials/`.
Any format is fine as long as the workflow can read it.

## Quick Mental Model

```text
[Theory.lean (+ optional Theory/*.lean)] + [materials/]
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
[scripts/refactor_derived.py]
  final local refactor sweep
        ↓
[Derived.refactored.preview.lean]
        ↓
[scripts/run_compression_pass.py]
  pass 1.2 exact-duplicate collapse with incremental repair
        ↓
[Derived.refactored.preview.lean]
        ↓
[scripts/run_proof_retarget_pass.py]
  pass 1.3 proof-retarget compression with incremental repair
        ↓
[Derived.refactored.preview.lean]
        ↓
[scripts/run_presentation_pass.py]
  optional pass 1.4 presentation shaping
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
  --context-file materials/example.md \
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
  --context-file materials/example.md \
  --max-iterations 40
```

Run the final refactor stages of `Derived.lean`:

```bash
uv run python scripts/atc_cli.py refactor
uv run python scripts/atc_cli.py compress
uv run python scripts/atc_cli.py retarget
uv run python scripts/atc_cli.py present
uv run python scripts/atc_cli.py rewrite
uv run python scripts/atc_cli.py review
```

Equivalent `Makefile` shortcuts remain available:

```bash
make seed SEED_ARGS="--context-file materials/example.md --seed-count 4"
make loop LOOP_ARGS="--max-iterations 40"
make pipeline PIPELINE_ARGS="--context-file materials/example.md --max-iterations 40"
make refactor
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
