# Runtime Details

This document keeps the detailed operational notes that were previously in the root README.

## Current Runtime Design

The main loop is `scripts/run_loop.py`. Its runtime paths are currently fixed in code:

- theory entry: `AutomatedTheoryConstruction/Theory.lean`
- accumulated theorems: `AutomatedTheoryConstruction/Derived.lean`
- temporary verification file: `AutomatedTheoryConstruction/Scratch.lean`
- initial seeds: `AutomatedTheoryConstruction/seeds.jsonl`
- runtime state: `data/`

`Theory.lean` remains the fixed public entry point, but it may import additional local files such as `AutomatedTheoryConstruction/Theory/*.lean`. The worker-facing theory context is built from the entry file plus its repo-local Lean imports.

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

- `AutomatedTheoryConstruction/Theory.lean`: base theory entry module
- `AutomatedTheoryConstruction/Theory/*.lean` (optional): local theory submodules imported by `Theory.lean`
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
- `materials/*`: optional papers, notes, and context files for seed generation
- `example/*`: reference examples not wired into `run_loop.py`

## Seed Generation Only

To regenerate `AutomatedTheoryConstruction/seeds.jsonl` without running the full loop:

```bash
uv run python scripts/generate_seeds_from_theory.py \
  --context-file path/to/context.tex \
  --seed-count 4
```

- Repeat `--context-file` to provide multiple files.
- The output path defaults to `AutomatedTheoryConstruction/seeds.jsonl`.
- Seed generation reads the `Theory.lean` entry file together with its repo-local imported theory modules, so splitting the theory under `AutomatedTheoryConstruction/Theory/` is supported.
- `materials/` is just a convenient place to keep these materials in the repo; any file path works.
- By default, this command first resets the active runtime state, clears archived/solved/counterexample state, resets `Scratch.lean` and `Derived.lean`, rebuilds the stable Lean targets, and then generates fresh seeds against that reset state.
- As part of that reset, the previous `AutomatedTheoryConstruction/seeds.jsonl` is removed before new seeds are generated.
- After seed generation finishes, the new `AutomatedTheoryConstruction/seeds.jsonl` is copied into `data/open_problems.jsonl`.
- If you want to regenerate only `seeds.jsonl` without resetting the runtime, add `--no-initialize-runtime-state`.

## One-Shot Pipeline

To generate `seeds.jsonl` from the active `Theory.lean` entry module, its imported local theory files, and article/context files, run `run_loop.py`, and then run the two-stage refactor in one go:

```bash
ATC_CODEX_TIMEOUT=390 \
uv run python scripts/run_pipeline.py \
  --article-file path/to/context.tex \
  --worker-command "uv run python scripts/codex_worker.py" \
  --worker-timeout 420 \
  --max-iteration 40
```

- Repeat `--article-file` when you want multiple context files.
- `--dry-run` prints the underlying commands without executing them.
- The wrapper uses the fixed active runtime files: `AutomatedTheoryConstruction/Theory.lean`, `AutomatedTheoryConstruction/seeds.jsonl`, and `AutomatedTheoryConstruction/Derived.lean`.
- `AutomatedTheoryConstruction/Theory.lean` may in turn import local theory files under `AutomatedTheoryConstruction/Theory/`.

## Worker Modes

Dry run with the mock worker:

```bash
ATC_WORKER_COMMAND="uv run scripts/mock_worker.py" \
uv run scripts/run_loop.py --enable-worker
```

Run with the Codex worker:

```bash
ATC_WORKER_COMMAND="uv run scripts/codex_worker.py" \
ATC_WORKER_TIMEOUT=420 \
ATC_CODEX_TIMEOUT=390 \
uv run scripts/run_loop.py --enable-worker
```

## Final Two-Stage Refactor For `Derived.lean`

After the main loop has accumulated enough theorems in `AutomatedTheoryConstruction/Derived.lean`, run the final cleanup in two passes.

Pass 1 performs the main structural refactor and writes a preview file:

```bash
uv run python scripts/refactor_derived.py \
  --worker-command "uv run python scripts/codex_worker.py" \
  --output-file AutomatedTheoryConstruction/Derived.refactored.preview.lean
```

When `--worker-timeout` is omitted for `scripts/refactor_derived.py`, the refactor worker defaults to no outer timeout. Set `--worker-timeout <seconds>` or `ATC_REFACTOR_DERIVED_WORKER_TIMEOUT` if you want a bound for this pass.

Pass 2 keeps the refactored theorem inventory but applies a review-focused non-semantic polish using the thin `codex exec` wrapper and the repository skills directly:

```bash
uv run python scripts/direct_refactor_derived.py \
  --input-file AutomatedTheoryConstruction/Derived.refactored.preview.lean \
  --output-file AutomatedTheoryConstruction/Derived.refactored.reviewed.lean
```

If `AutomatedTheoryConstruction/Derived.refactored.reviewed.lean` already exists and you want Codex to continue editing it without copying from the preview again, use:

```bash
uv run python scripts/direct_refactor_derived.py --skip-copy
```

## Initialization Behavior

By default, `scripts/generate_seeds_from_theory.py` initializes a fresh runtime before generating `AutomatedTheoryConstruction/seeds.jsonl`. This reset does the following:

- overwrite `data/open_problems.jsonl` from `AutomatedTheoryConstruction/seeds.jsonl`
- reset `data/archived_problems.jsonl`
- reset `data/solved_problems.jsonl`
- reset `data/counterexamples.jsonl`
- reset `data/formalization_memory.json`
- reset `AutomatedTheoryConstruction/Scratch.lean`
- reset `AutomatedTheoryConstruction/Derived.lean`
- delete `AutomatedTheoryConstruction/Derived.refactored.preview.lean` if present
- delete `AutomatedTheoryConstruction/Derived.refactored.reviewed.lean` if present
- run `lake build` for `AutomatedTheoryConstruction.Theory` and `AutomatedTheoryConstruction.Derived`

After the new seeds are generated, the script writes them to `AutomatedTheoryConstruction/seeds.jsonl` and mirrors them into `data/open_problems.jsonl`.

If you run `scripts/run_loop.py` directly, it still defaults to `--initialize-on-start` and performs the same reset before beginning the loop.

If you want to continue from the current runtime state and keep accumulated theorems in `Derived.lean`, use:

```bash
ATC_WORKER_COMMAND="uv run scripts/codex_worker.py" \
ATC_WORKER_TIMEOUT=420 \
ATC_CODEX_TIMEOUT=390 \
uv run scripts/run_loop.py --enable-worker --no-initialize-on-start
```

If you want the loop to consider adding a main theorem whenever `Derived.lean` has gained another `N` verified theorems, set `--main-theorem-interval N`. For example:

```bash
ATC_WORKER_COMMAND="uv run scripts/codex_worker.py" \
ATC_WORKER_TIMEOUT=420 \
ATC_CODEX_TIMEOUT=390 \
uv run scripts/run_loop.py \
  --enable-worker \
  --no-initialize-on-start \
  --main-theorem-interval 10 \
  --main-theorem-formalize-worker-timeout 900 \
  --main-theorem-repair-worker-timeout 600
```

The auto main-theorem path uses the same worker stack and supports separate limits through `--main-theorem-formalize-worker-timeout`, `--main-theorem-repair-worker-timeout`, `--main-theorem-verify-timeout`, and `--main-theorem-formalization-retry-budget-sec`.

`scripts/run_pipeline.py` prefers initialization in the seed-generation stage, then runs `scripts/run_loop.py --no-initialize-on-start` to avoid doing the same reset twice.

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
- `--open-problem-failure-threshold`
- `--priority-refresh-theorem-interval`
- `--main-theorem-interval`
- `--main-theorem-verify-timeout`
- `--main-theorem-formalization-retry-budget-sec`

## Open Problem Queue

`scripts/run_loop.py` tracks per-problem queue metadata:

- `priority`
- `priority_rationale`
- `failure_count`

Open problem priorities are refreshed by a dedicated worker prompt whenever unevaluated `unknown` problems exist, and otherwise after `Derived.lean` has gained enough new theorems during the current run, by default every `5` additional verified theorems. Priorities are refreshed across the full tracked problem set: the active `open` queue plus `archived` problems kept only for priority context.

`data/open_problems.jsonl` stores only the active solver queue. Any tracked problem whose priority is `low`, or whose `failure_count` has reached the failure threshold, by default `2`, is moved to `data/archived_problems.jsonl`. Archived problems are not solver-eligible, but they remain visible during future priority refreshes so the worker can judge new and active problems against older low-value or repeatedly failed statements.

## Runtime Artifacts

The loop stores its state in `data/`:

- `data/open_problems.jsonl`
- `data/archived_problems.jsonl`
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
- `example/CCG`, `example/Equational_theory`, and `example/provability` are examples only; they are not selected by a runtime flag today. Aristotle is used to generate `Theory.lean`.
- `expand` suggestions are deduplicated before state update.
- `formalize` and `repair` are separate task types, even if they use the same prompt file by default.
