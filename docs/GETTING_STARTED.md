# Getting Started

This page is the recommended first-read for using this repository.

## Order

1. Set up Lean 4 and Mathlib.
2. Set up Codex.
3. Enable `lean-lsp-mcp`.
4. Put your base theory code in `AutomatedTheoryConstruction/Theory/Core.lean`.
5. Avoid notation or symbols that are likely to conflict with Mathlib.
6. Put reference materials for seed generation under `materials/`.
7. Generate seeds or run the loop.

Use the toolchain from `lean-toolchain`, then run `lake build` in the repo.
Make sure the Codex CLI works in this repository before running the worker loop.
Set up `lean-lsp-mcp` in the environment where you want Lean-aware agent/tool support.
Keep `AutomatedTheoryConstruction/Theory.lean` as the entry point that imports your local theory files.
If you split your theory across multiple files under `AutomatedTheoryConstruction/Theory/`, add the corresponding `import` lines to `AutomatedTheoryConstruction/Theory.lean`.
Reusing common Mathlib notation names without a good reason will make the Lean side harder to maintain.
Any format is fine for seed-generation reference materials as long as the workflow can read it.
Pass the files you want to use with `--context-file`.

## First File To Edit

Start with:

- `AutomatedTheoryConstruction/Theory/Core.lean`

Then check that the project still builds:

```bash
make build
make check
```

## Reference Materials

For seed generation, you can place supporting material under `materials/`, for example:

- notes
- drafts
- papers
- problem sketches

Examples:

```bash
uv run python scripts/atc_cli.py seed \
  --context-file materials/notes.md \
  --seed-count 4
```

```bash
uv run python scripts/atc_cli.py seed \
  --context-file materials/paper.pdf \
  --seed-count 4
```

## After Setup

Useful next pages:

- [`USER_GUIDE.md`](USER_GUIDE.md)
- [`REPO_MAP.md`](REPO_MAP.md)
