# User Guide

This page is for normal operation after initial setup. For first-time setup, read [`GETTING_STARTED.md`](GETTING_STARTED.md) first.

## Operational Mental Model

```text
[Theory.lean (+ optional Theory/*.lean)] + [research_agenda.md] + [optional materials/]
        ↓
seed generation
        ↓
[seeds.jsonl]
        ↓
loop: generate -> formalize -> verify -> repair
        ↓
[Scratch.lean] temporary verification target
        ↓
[Derived.lean] accumulated verified theorems
        ↓
optional cleanup and split-based refactor stages
```

The important separation is:

- you edit the base theory and agenda
- the loop edits `Derived.lean`, `Scratch.lean`, and runtime data

If you need ownership boundaries, keep [`REPO_MAP.md`](REPO_MAP.md) open alongside this guide.

## What You Usually Edit

For a custom theory, the normal edit set is:

- `AutomatedTheoryConstruction/Theory.lean`
- `AutomatedTheoryConstruction/Theory/*.lean`
- `AutomatedTheoryConstruction/research_agenda.md`
- `materials/` when you want reusable deep-research context to inform generation and evaluation
- `AutomatedTheoryConstruction/seeds.jsonl` when you want to hand-curate initial problems

`Theory.lean` stays the public entry point. If the theory grows, keep imports there and move detailed definitions or helper lemmas into `AutomatedTheoryConstruction/Theory/`.
If a file starts importing multiple local modules, treat that as a dependency change: avoid cycles, do not rely on another file's transitive imports implicitly, and confirm `Theory.lean` still checks cleanly.
If theorem statements start getting long because the same assumption bundle is repeated, prefer introducing a small reusable `def`/`abbrev` in the theory layer before letting the loop accumulate longer theorem faces in `Derived.lean`.

`materials/` is the recommended place to keep organized deep-research output:

- literature summaries
- direct source-link lists
- extracted problem families
- evaluation rubrics or structural-theme notes

The important boundary is that `materials/` is optional external context.
It can influence prompts, but it should not be treated as core loop state and should not be folded into `theory_state.json`.
If a summary report inside `materials/` becomes old, keep it as context but treat it as lower-confidence than source links or primary papers.

## Common Commands

The unified operational entrypoint is:

```bash
uv run python scripts/atc_cli.py --help
```

If `configs/atc.json` exists, `scripts/atc_cli.py` picks it up automatically.
You can inspect the resolved config with:

```bash
uv run python scripts/atc_cli.py config show
```

Core checks:

```bash
make build
make check
```

## Daily Workflows

### Regenerate seeds

```bash
uv run python scripts/atc_cli.py seed \
  --seed-count 4
```

Optional extra reference material can be attached ad hoc:

```bash
uv run python scripts/atc_cli.py seed \
  --context-file path/to/context.pdf \
  --seed-count 4
```

For reusable domain knowledge, prefer curating it under `materials/` instead of repeatedly passing one-off files.
That keeps deep research available across prioritization, expansion, and paper-claim work.
When a report may be out of date, keep the report for structure and wording, but use source-link bundles for novelty checks and literature positioning.

### Regenerate `research_agenda.md` from a deep-research report

```bash
make materials-cache
make research-agenda REPORT_FILE=materials/your_report.md
```

This refreshes `data/materials_cache` and then writes directly to `AutomatedTheoryConstruction/research_agenda.md`.
If you want to inspect the composed prompt first, add:

```bash
uv run python scripts/atc_cli.py research-agenda \
  --report-file materials/your_report.md \
  --preview-prompt
```

### Run the main loop

```bash
uv run python scripts/atc_cli.py loop
```

Equivalent `Makefile` shortcut:

```bash
make loop
```

`make loop` resets runtime state on start. If you want to keep the current queue and `Derived.lean`, use:

```bash
make loop-continue
```

### Run a larger one-shot pipeline

```bash
uv run python scripts/atc_cli.py pipeline \
  --max-iterations 40
```

Equivalent shortcut:

```bash
make pipeline PIPELINE_ARGS="--max-iterations 40"
```

### Run the final whole-file refactor passes

```bash
cp AutomatedTheoryConstruction/Derived.lean AutomatedTheoryConstruction/Derived.refactored.preview.lean
uv run python scripts/atc_cli.py rewrite
uv run python scripts/atc_cli.py review
```

`rewrite` is the pass 1.5 cleanup stage. `review` is the pass 2.0 review-focused cleanup stage.

### Materialize generated chunk files

```bash
uv run python scripts/atc_cli.py materialize-generated
```

This splits `Derived.lean` into `AutomatedTheoryConstruction/Generated/C000x_*.lean`, rebuilds `Manifest.lean` and `catalog.json`, and performs generated-level verification and repair.

If you want the bundled end-to-end shortcut for the whole refactor path:

```bash
make refactor-to-generated
```

## Worker Modes

### Mock worker for smoke runs

```bash
uv run python scripts/atc_cli.py loop \
  --worker-command "uv run scripts/mock_worker.py" \
  --max-iterations 1
```

### Codex-backed worker

```bash
uv run python scripts/atc_cli.py loop \
  --worker-command "uv run scripts/codex_worker.py" \
  --worker-timeout 420 \
  --codex-timeout 390 \
  --formalization-retry-budget-sec 900 \
  --max-same-error-streak 5
```

## Custom Proof Engine

Planning and Lean verification are deliberately separated.
If you want to replace only the final verification step used for `Scratch.lean`, set `ATC_PROOF_EXECUTOR` before running the CLI and keep the rest of the worker loop unchanged.

For the full JSON contract and replacement steps, read [`PROOF_EXECUTOR.md`](PROOF_EXECUTOR.md).

## More Detail

For implementation-oriented runtime behavior, see [`../design/RUNTIME.md`](../design/RUNTIME.md).
For the full documentation index, see [`README.md`](README.md).
