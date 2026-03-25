# Automated Theory Construction

It implements an automated theory-construction loop on top of Lean 4 + Mathlib. Given a base theory, the system proposes candidate statements, attempts to formalize and prove them in Lean, verifies successful results, and accumulates the verified theorems into the derived theory.

For more details and generation examples, please see here.
- [Blog post: Growing Theories with LLMs and Lean](https://tukamilano.github.io/automated-theory-construction-lean/research/lean/llm/2026/03/23/automated-theory-construction-with-llms.html)
- [Application to provability logic](https://gist.github.com/tukamilano/4fdcbc3c8d3836654ae9e7d27a73e3de) (update 3.25)

As the developer is not an expert for these theories, any feedback, suggestions, or contributions are very welcome. Please open an issue or a pull request.

## Quick Mental Model

```text
[Theory.lean] + [articles / notes / paper]
        ↓
[scripts/generate_seeds_from_theory.py]
  generate initial open problems
        ↓
[seeds.jsonl]
        ↓
+-------------------------------------------+
| [Theory.lean]                             |
|   base symbols + axioms                   |
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

For a first-time reader, the core idea is:

- `AutomatedTheoryConstruction/Theory.lean` defines the starting symbols and axioms
- `AutomatedTheoryConstruction/Scratch.lean` is the temporary file used for Lean verification
- `AutomatedTheoryConstruction/Derived.lean` stores the verified theorems discovered so far
- `scripts/run_loop.py` orchestrates the full loop

The current design is a single runtime pipeline with:

- deterministic orchestration in Python
- Lean verification through `Scratch.lean`
- verified theorem accumulation in `Derived.lean`
- worker-driven stages for statement formalization, proving, formalization/repair, and expansion

## Current Runtime Design

The main loop is `scripts/run_loop.py`. Its runtime paths are currently fixed in code:

- theory: `AutomatedTheoryConstruction/Theory.lean`
- accumulated theorems: `AutomatedTheoryConstruction/Derived.lean`
- temporary verification file: `AutomatedTheoryConstruction/Scratch.lean`
- initial seeds: `AutomatedTheoryConstruction/seeds.jsonl`
- runtime state: `data/`

So the current implementation is not yet a generic multi-theory runner. To change the active theory, edit those fixed files rather than expecting a theory selector CLI.

Each iteration runs the following stages:

1. Pick the next open problem deterministically.
2. If the problem is not already Lean-formal, try `prover_statement` to turn it into a Lean-ready statement.
3. Run `prover` to choose `proof`, `counterexample`, or `stuck`.
4. Run `formalize`, then `lake env lean AutomatedTheoryConstruction/Scratch.lean`.
5. If verification fails, run `repair` until the retry budget is exhausted.
6. If verification succeeds, append the theorem body from `Scratch.lean` into `Derived.lean`.
7. Run `expand` to suggest additional problems.
8. Apply deterministic state updates to `open`, `solved`, and `counterexamples`.

Open problems may be either Lean-formal statements or semi-formal research prompts. If a problem cannot be formalized, it stays open.

## Repository Layout

- `AutomatedTheoryConstruction/Theory.lean`: base theory, symbols, and axioms
- `AutomatedTheoryConstruction/Derived.lean`: verified theorem accumulation target
- `AutomatedTheoryConstruction/Scratch.lean`: temporary verification artifact
- `scripts/run_loop.py`: main orchestrator
- `scripts/codex_worker.py`: worker wrapper around `codex exec`
- `scripts/mock_worker.py`: contract-compatible mock worker
- `scripts/worker_client.py`: subprocess worker client and timeout handling
- `scripts/lean_verify.py`: Lean verification wrapper
- `scripts/state_update.py`: deterministic JSONL state transitions
- `scripts/append_derived.py`: append verified theorems to `Derived.lean`
- `prompts/prover_statement_formalizer.md`: statement-formalization prompt
- `prompts/prover_simple.md`: prover prompt
- `prompts/formalizer_simple.md`: formalize/repair prompt
- `prompts/new_problem_expander.md`: expansion prompt
- `AutomatedTheoryConstruction/seeds.jsonl`: currently active seed queue
- `example/*`: reference examples not wired into `run_loop.py`

## Requirements

- Lean toolchain from `lean-toolchain`
- Lake + Mathlib dependencies
- Python
- `uv`
- Codex CLI if you want to use `scripts/codex_worker.py`

For interactive Lean work with Codex, `lean-lsp-mcp` is also useful, but it is not part of the runtime loop itself.

## Setup

Build the Lean project once:

```bash
lake build
```

Smoke-check the verification path:

```bash
lake env lean AutomatedTheoryConstruction/Scratch.lean
```

## Quick Start

Edit the active theory:

- `AutomatedTheoryConstruction/Theory.lean`
- `AutomatedTheoryConstruction/seeds.jsonl`

### One-Shot Pipeline

To generate `seeds.jsonl` from `Theory.lean` plus article/context files, run `run_loop.py`, and then run the two-stage refactor in one go:

```bash
ATC_CODEX_TIMEOUT=390 \
uv run python scripts/run_pipeline.py \
  --article-file docs/context.tex \
  --worker-command "uv run python scripts/codex_worker.py" \
  --worker-timeout 420 \
  --max-iteration 40
```

- Repeat `--article-file` when you want multiple context files.
- `--dry-run` prints the underlying commands without executing them.
- The wrapper uses the fixed active runtime files: `AutomatedTheoryConstruction/Theory.lean`, `AutomatedTheoryConstruction/seeds.jsonl`, and `AutomatedTheoryConstruction/Derived.lean`.

Then choose a worker mode.

### Dry Run With Mock Worker

This exercises the loop and state transitions without calling Codex:

```bash
ATC_WORKER_COMMAND="uv run scripts/mock_worker.py" \
uv run scripts/run_loop.py --enable-worker
```

### Run With Codex Worker

```bash
ATC_WORKER_COMMAND="uv run scripts/codex_worker.py" \
ATC_WORKER_TIMEOUT=420 \
ATC_CODEX_TIMEOUT=390 \
uv run scripts/run_loop.py --enable-worker
```

### Final Two-Stage Refactor For `Derived.lean`

After the main loop has accumulated enough theorems in `AutomatedTheoryConstruction/Derived.lean`,
run the final cleanup in two passes.

Pass 1 performs the main structural refactor and writes a preview file:

```bash
uv run python scripts/refactor_derived.py \
  --worker-command "uv run python scripts/codex_worker.py" \
  --output-file AutomatedTheoryConstruction/Derived.refactored.preview.lean
```

When `--worker-timeout` is omitted for `scripts/refactor_derived.py`, the refactor worker now defaults to no outer timeout.
Set `--worker-timeout <seconds>` (or `ATC_REFACTOR_DERIVED_WORKER_TIMEOUT`) if you want a bound for this pass.

Pass 2 keeps the refactored theorem inventory but applies a review-focused non-semantic polish using
the thin `codex exec` wrapper and the repository skills directly. No dedicated review prompt file is
needed:

```bash
uv run python scripts/direct_refactor_derived.py \
  --input-file AutomatedTheoryConstruction/Derived.refactored.preview.lean \
  --output-file AutomatedTheoryConstruction/Derived.refactored.reviewed.lean
```

If `AutomatedTheoryConstruction/Derived.refactored.reviewed.lean` already exists and you want Codex
to continue editing it without copying from the preview again, use:

```bash
uv run python scripts/direct_refactor_derived.py --skip-copy
```

## Initialization Behavior

By default, `scripts/run_loop.py` starts with `--initialize-on-start`, which means it will:

- overwrite `data/open_problems.jsonl` from `AutomatedTheoryConstruction/seeds.jsonl`
- reset `data/solved_problems.jsonl`
- reset `data/counterexamples.jsonl`
- reset `data/pruned_open_problems.jsonl`
- reset `data/formalization_memory.json`
- reset `AutomatedTheoryConstruction/Scratch.lean`
- reset `AutomatedTheoryConstruction/Derived.lean`
- delete `AutomatedTheoryConstruction/Derived.refactored.preview.lean` if present
- delete `AutomatedTheoryConstruction/Derived.refactored.reviewed.lean` if present
- run `lake build` for `AutomatedTheoryConstruction.Theory` and `AutomatedTheoryConstruction.Derived`

If you want to continue from the current runtime state and keep accumulated theorems in `Derived.lean`, use:

```bash
ATC_WORKER_COMMAND="uv run scripts/codex_worker.py" \
ATC_WORKER_TIMEOUT=420 \
ATC_CODEX_TIMEOUT=390 \
uv run scripts/run_loop.py --enable-worker --no-initialize-on-start
```

This reset behavior is important: the current loop treats initialization as "start a fresh run from seeds".

## Worker Configuration

Shared worker settings:

- `ATC_WORKER_COMMAND`
- `ATC_WORKER_TIMEOUT`

Task-specific overrides:

- `ATC_PROVER_WORKER_COMMAND`
- `ATC_PROVER_WORKER_TIMEOUT`
- `ATC_PROVER_STATEMENT_WORKER_COMMAND`
- `ATC_PROVER_STATEMENT_WORKER_TIMEOUT`
- `ATC_FORMALIZE_WORKER_COMMAND`
- `ATC_FORMALIZE_WORKER_TIMEOUT`
- `ATC_REPAIR_WORKER_COMMAND`
- `ATC_REPAIR_WORKER_TIMEOUT`
- `ATC_PRIORITIZE_OPEN_PROBLEMS_WORKER_COMMAND`
- `ATC_PRIORITIZE_OPEN_PROBLEMS_WORKER_TIMEOUT`

Useful Codex worker settings:

- `ATC_CODEX_TIMEOUT`: inner timeout used by `scripts/codex_worker.py`
- `ATC_CODEX_MODEL`: optional model override for `codex exec`
- `ATC_PROVER_CODEX_MODEL`: optional prover-only model override
- `ATC_PROVER_CODEX_TIMEOUT`: optional prover-only inner timeout override
- `ATC_PROVER_STATEMENT_CODEX_MODEL`: optional prover-statement-only model override
- `ATC_PROVER_STATEMENT_CODEX_TIMEOUT`: optional prover-statement-only inner timeout override

You can also override the same settings through CLI flags such as:

- `--worker-command`
- `--worker-timeout`
- `--prover-worker-command`
- `--prover-worker-timeout`
- `--prover-statement-worker-command`
- `--prover-statement-worker-timeout`
- `--formalize-worker-command`
- `--formalize-worker-timeout`
- `--repair-worker-command`
- `--repair-worker-timeout`
- `--prioritize-open-problems-worker-command`
- `--prioritize-open-problems-worker-timeout`
- `--open-problem-prune-threshold`
- `--open-problem-failure-prune-threshold`
- `--priority-refresh-theorem-interval`

## Open Problem Queue

To keep `data/open_problems.jsonl` from growing without bound, `scripts/run_loop.py` now tracks
per-problem queue metadata:

- `priority`
- `priority_rationale`
- `failure_count`

Open problem priorities are refreshed by a dedicated worker prompt whenever unevaluated `unknown`
problems exist, and otherwise after `Derived.lean` has gained enough new theorems during the
current run (default every `5` additional verified theorems). The queue is then sorted in priority
order: `high`, then `medium`, then unevaluated `unknown`, then `low`. Problems whose
`failure_count` reaches the failure threshold (default `2`) are kept in the queue but moved to the
end.

When the open queue exceeds the prune threshold (default `30`), the loop removes every problem
whose priority is `low` or whose `failure_count` is at least the failure threshold. Pruned rows are
removed from `open_problems.jsonl` and appended to `data/pruned_open_problems.jsonl` for
auditability.

## Runtime Artifacts

The loop stores its state in `data/`:

- `data/open_problems.jsonl`
- `data/pruned_open_problems.jsonl`
- `data/solved_problems.jsonl`
- `data/counterexamples.jsonl`
- `data/formalization_memory.json`

`data/formalization_memory.json` stores same-problem history across statement formalization, formalization, and repair attempts.

## Lean Module Contract

- `Theory.lean` defines the base objects and axioms.
- `Derived.lean` contains only verified theorems that have passed Lean checking.
- `Scratch.lean` is the temporary file used for each verification attempt.

The verification command is:

```bash
lake env lean AutomatedTheoryConstruction/Scratch.lean
```

## Notes

- `scripts/run_loop.py` currently assumes the semigroup-like seed file path and fixed module layout.
- `example/CCG`, `example/Equational_theory`, and `example/provability` are examples only; they are not selected by a runtime flag today. Aristotle is used to generate Theory.lean.
- `expand` suggestions are deduplicated before state update.
- `formalize` and `repair` are separate task types, even if they use the same prompt file by default.

## License

This repository is licensed under the MIT License. See `LICENSE`.

## Reference

- Xin et al. (2025). *BFS-Prover-V2*.
- Lev Beklemishev and Daniyar Shamkanov. *Some abstract versions of Gödel's second incompleteness theorem based on non-classical logics*. arXiv:1602.05728.
- Elliott H. Lieb and Jakob Yngvason. *The physics and mathematics of the second law of thermodynamics*. Physics Reports, 310(1):1–96, 1999.
- Antonius J.C. Hurkens. *A simplification of Girard's paradox*. *In Proceedings of the Typed Lambda Calculi and Applications.*Mariangiola Dezani-Ciancaglini and Gordon Plotkin (Eds.), Springer, Berlin, 266–278.

## Acknowledgements

The prompting strategy for solving Lean problems was partially inspired by a private repository (`kmd710/lean4-codex-skills`).

This repository also includes one file that was copied and then adapted from SnO2WMaN's `provability-toy` repository:
<https://github.com/SnO2WMaN/provability-toy>
