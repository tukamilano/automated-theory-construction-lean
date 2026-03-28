# Automated Theory Construction

This project builds and verifies nontrivial mathematical structure **automatically** in Lean 4.

Given only a small axiom system, it generates candidate statements, attempts formal proofs, and accumulates verified theorems into a growing derived theory — without manually specifying targets in advance.

Unlike conventional workflows that aim directly at predefined theorems, this system **constructs theory bottom-up**, continuously generating and refining local statements in a way that mirrors — and scales — experimental mathematical practice.

## Core Claim

> Starting from minimal axioms, the system autonomously discovers and verifies structured theory that typically requires deliberate human design.

## Highlighted Result: CCR → Fock Space Structure

From a minimal axiom system consisting only of:
- creation / annihilation operators
- a vacuum axiom

this system automatically derives:

- ladder operator structure  
- eigenvalue laws for the number operator  
- linear independence of generated ket families  
- a finite-dimensional impossibility theorem  
- structural representation results of the generated span  

All results are:
- fully formalized in Lean 4  
- mechanically verified  
- produced through the automated loop (not manually curated proofs)  

Crucially, **no explicit representation theory or Fock-space structure is assumed upfront**.

The system recovers these structures purely through iterative exploration of the axioms.

[Application to canonical commutation relations in quantum mechanics](https://gist.github.com/tukamilano/311759e88a5ec11647aa2b83f42ce8a1)

For more details and generation examples, please see here.
- [Progress](https://tukamilano.github.io/automated-theory-construction-lean/notes/draft/2026/03/27/progress.html) (update 3.27)
- [Application to provability logic](https://gist.github.com/tukamilano/ba2c5719e0c5e2e1093b5b4dd174c182) (update 3.25)
- [Application to Pure Type System λU⁻](https://gist.github.com/tukamilano/cc1f22efd19a7553c9b9883f30e119af)
- [Application to canonical commutation relations in quantum mechanics](https://gist.github.com/tukamilano/311759e88a5ec11647aa2b83f42ce8a1)

## Why This Matters

Most current theorem provers focus on *proving given statements*.

This project targets a different layer:

- generating the statements themselves  
- organizing them into coherent theory  
- and doing so without predefined goals  

In other words, this shifts the problem from **proof automation** to **theory construction**.

This distinction is critical:

- proof search scales within a fixed space  
- theory construction expands the space itself  

The CCR example demonstrates that nontrivial mathematical structure can emerge purely from local exploration of minimal axioms — without embedding domain knowledge or target representations in advance.

## Mechanism (High-Level)

1. Start from a base theory (`Theory.lean`)  
2. Generate candidate statements (bottom-up, local transformations)  
3. Attempt formalization and proof in Lean  
4. Verify and append successful theorems (`Derived.lean`)  
5. Recycle failures into refined subproblems  

This loop runs continuously, producing a growing body of verified results.

## Design Principle

> Do not aim directly at the final theorem.  
> Instead, generate the surrounding structure until the theorem becomes inevitable.

## 3-Minute Quick Start

If you want the fastest possible first run, use the bundled example theory and the mock worker.
This path does not require Codex CLI.

Requirements:

- Lean toolchain from `lean-toolchain`
- Lake + Mathlib dependencies
- Python
- `uv`

Run:

```bash
make build
make check-scratch
WORKER_COMMAND="uv run scripts/mock_worker.py" make loop LOOP_ARGS="--max-iterations 1"
```

What this does:

- builds the project
- checks that `AutomatedTheoryConstruction/Scratch.lean` verifies
- runs one loop iteration against the current theory and seed state

Notes:

- `make loop` resets the runtime state by default. Use `make loop-continue` if you want to keep the current `Derived.lean` and queue state.
- If you want a real LLM-backed run instead of the mock worker, see [Run With Codex Worker](#run-with-codex-worker).

## Use Your Own Theory

To switch from the bundled example to your own theory, edit:

- `AutomatedTheoryConstruction/Theory.lean`
- `AutomatedTheoryConstruction/Theory/*.lean` as needed for local theory submodules
- `AutomatedTheoryConstruction/seeds.jsonl` if you want to provide your own initial problems

`Theory.lean` remains the public entry point. If your theory grows beyond one file, keep the imports there and move detailed definitions or helper lemmas under `AutomatedTheoryConstruction/Theory/`.

If you want to regenerate seeds from the current theory plus context files:

```bash
make seed SEED_ARGS="--context-file path/to/context.tex --seed-count 4"
```

That command refreshes `AutomatedTheoryConstruction/seeds.jsonl` and resets the active runtime state unless you pass the corresponding no-initialize flag directly to the script.

## Run With Codex Worker

If you have Codex CLI available and want the actual worker-backed loop:

```bash
make loop
```

This expands to the default worker command in the `Makefile`:

```bash
ATC_WORKER_COMMAND="uv run scripts/codex_worker.py" \
ATC_WORKER_TIMEOUT=420 \
ATC_CODEX_TIMEOUT=390 \
uv run scripts/run_loop.py --enable-worker
```

If you want to keep the current runtime state instead of reinitializing it:

```bash
make loop-continue
```

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

## Common Commands

The repository includes a small `Makefile` wrapper for common tasks:

```bash
make help
```

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
make seed SEED_ARGS="--context-file path/to/context.tex --seed-count 4"
```

Run the one-shot pipeline from seed generation through refactor:

```bash
make pipeline PIPELINE_ARGS="--article-file path/to/context.tex --max-iterations 40"
```

Run the final two-stage cleanup of `Derived.lean`:

```bash
make refactor
make review
```

If you prefer the underlying scripts directly instead of the `Makefile` wrappers:

```bash
uv run python scripts/refactor_derived.py \
  --worker-command "uv run python scripts/codex_worker.py" \
  --output-file AutomatedTheoryConstruction/Derived.refactored.preview.lean
```

```bash
uv run python scripts/direct_refactor_derived.py \
  --input-file AutomatedTheoryConstruction/Derived.refactored.preview.lean \
  --output-file AutomatedTheoryConstruction/Derived.refactored.reviewed.lean
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

