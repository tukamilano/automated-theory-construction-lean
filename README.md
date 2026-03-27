# Automated Theory Construction

This repository implements an automated theory-construction loop on top of Lean 4 + Mathlib. Given a base theory, the system proposes candidate statements, attempts to formalize and prove them in Lean, verifies successful results, and accumulates the verified theorems into the derived theory.

Current claim:
- the repository demonstrates an end-to-end loop for theory-relative problem generation, Lean verification, verified theorem accumulation, and occasional main-theorem attempts
- the repository is intended as a research prototype for automated theory construction in Lean, not yet as a validated measure of mathematical interestingness or novelty

Current non-claim:
- it does not yet establish, through sufficient human validation, that the generated theorems are consistently interesting, important, or publishable
- it does not yet claim benchmarked superiority over simpler conjecture-generation or theorem-proving baselines

For more details and generation examples, please see here.
- [Progress](https://tukamilano.github.io/automated-theory-construction-lean/notes/draft/2026/03/27/progress.html) (update 3.27)
- [Application to provability logic](https://gist.github.com/tukamilano/ba2c5719e0c5e2e1093b5b4dd174c182) (update 3.25)
- [Application to Pure Type System λU⁻](https://gist.github.com/tukamilano/cc1f22efd19a7553c9b9883f30e119af)
- [Application to canonical commutation relations in quantum mechanics](https://gist.github.com/tukamilano/311759e88a5ec11647aa2b83f42ce8a1)

As the developer is not an expert for these theories, any feedback, suggestions, or contributions are very welcome. Please open an issue or a pull request.

## Quick Mental Model

```text
[Theory.lean (+ optional Theory/*.lean)] + [docs/articles / notes / paper]
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
  structural refactor
        ↓
[Derived.refactored.preview.lean]
        ↓
[scripts/direct_refactor_derived.py]
  review-focused non-semantic cleanup
        ↓
[Derived.refactored.reviewed.lean]
```

For a first-time reader, the core files are:

- `AutomatedTheoryConstruction/Theory.lean`: theory entry module
- `AutomatedTheoryConstruction/Theory/*.lean` (optional): local supporting definitions and lemmas imported by `Theory.lean`
- `AutomatedTheoryConstruction/Scratch.lean`: temporary Lean verification target
- `AutomatedTheoryConstruction/Derived.lean`: accumulated verified theorems
- `scripts/run_loop.py`: main loop

## Setup

Requirements:

- Lean toolchain from `lean-toolchain`
- Lake + Mathlib dependencies
- Python
- `uv`
- Codex CLI if you want to use `scripts/codex_worker.py`

Build the project once:

```bash
lake build
```

or:

```bash
make build
```

Smoke-check the verification path:

```bash
lake env lean AutomatedTheoryConstruction/Scratch.lean
```

or:

```bash
make check-scratch
```

The repository also includes a small `Makefile` wrapper for common tasks:

```bash
make help
```

## Quick Start

Edit the active theory inputs:

- `AutomatedTheoryConstruction/Theory.lean`
- `AutomatedTheoryConstruction/Theory/*.lean` as needed for local theory submodules
- `AutomatedTheoryConstruction/seeds.jsonl`

`Theory.lean` remains the public entry point. If your theory grows beyond one file, keep the imports there and move detailed definitions or helper lemmas under `AutomatedTheoryConstruction/Theory/`.

If you want to regenerate seeds from theory plus context files:

```bash
uv run python scripts/generate_seeds_from_theory.py \
  --context-file path/to/context.tex \
  --seed-count 4
```

or:

```bash
make seed SEED_ARGS="--context-file path/to/context.tex --seed-count 4"
```

If you want to run the main loop with the Codex worker:

```bash
ATC_WORKER_COMMAND="uv run scripts/codex_worker.py" \
ATC_WORKER_TIMEOUT=420 \
ATC_CODEX_TIMEOUT=390 \
uv run scripts/run_loop.py --enable-worker
```

or:

```bash
make loop
```

If you want a one-shot pipeline from seed generation through refactor:

```bash
ATC_CODEX_TIMEOUT=390 \
uv run python scripts/run_pipeline.py \
  --article-file path/to/context.tex \
  --worker-command "uv run python scripts/codex_worker.py" \
  --worker-timeout 420 \
  --max-iteration 40
```

or:

```bash
make pipeline PIPELINE_ARGS="--article-file path/to/context.tex --max-iterations 40"
```

If you want the final two-stage cleanup of `Derived.lean`:

```bash
uv run python scripts/refactor_derived.py \
  --worker-command "uv run python scripts/codex_worker.py" \
  --output-file AutomatedTheoryConstruction/Derived.refactored.preview.lean
```

or:

```bash
make refactor
```

```bash
uv run python scripts/direct_refactor_derived.py \
  --input-file AutomatedTheoryConstruction/Derived.refactored.preview.lean \
  --output-file AutomatedTheoryConstruction/Derived.refactored.reviewed.lean
```

or:

```bash
make review
```

## More Details

Detailed runtime behavior, initialization semantics, worker configuration, queue metadata, and extended command examples are documented in [RUNTIME.md](RUNTIME.md).

## License

This repository is licensed under the MIT License. See `LICENSE`.

## Reference

- Xin et al. (2025). *BFS-Prover-V2*.
- Lev Beklemishev and Daniyar Shamkanov. *Some abstract versions of Gödel's second incompleteness theorem based on non-classical logics*. arXiv:1602.05728.
- Antonius J.C. Hurkens. *A simplification of Girard's paradox*. *In Proceedings of the Typed Lambda Calculi and Applications.*Mariangiola Dezani-Ciancaglini and Gordon Plotkin (Eds.), Springer, Berlin, 266-278.
- Girard, J.-Y. "Interprétation fonctionnelle et élimination des coupures de l'arithmétique d'ordre supérieur." Thèse de doctorat d'état, 1972.
- Coquand, T. "An Analysis of Girard's Paradox." LICS 1986.

## Acknowledgements

The prompting strategy for solving Lean problems was partially inspired by a private repository (`kmd710/lean4-codex-skills`).

This repository also includes one file that was copied and then adapted from SnO2WMaN's `provability-toy` repository:
<https://github.com/SnO2WMaN/provability-toy>
