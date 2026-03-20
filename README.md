# Automated Theory Construction (Minimal Prototype)

This repository contains a minimal prototype for iterative theory growth in formal systems, where new statements are generated, tested, and accumulated from a given set of axioms and inference rules.

The current loop is:

1. Pick one open problem
2. Attempt proof / counterexample / stuck
3. Formalize and verify in Lean
4. Update state files
5. Reuse verified theorems from `Derived.lean`

## Current Scope

Implemented:

- Lean module scaffold: `Theory.lean`, `Derived.lean`, `Scratch.lean`
- `SemigroupLike01` axiom class (left idempotent, duplicate absorption, central swap)
- Data/state files: open / solved / counterexamples (JSONL)
- Natural-language proof notes in `data/proof_notes/`
- Same-problem formalization history in `data/formalization_memory.json`
- Deterministic state updates with atomic JSONL writes
- Auto-initialize from seeds on startup (default on)
- Orchestrator-to-worker wiring for prover/formalize/repair/expand tasks
- Prover interface contract in `.codex/skills`

## Repository Layout

- `AutomatedTheoryConstruction/Theory.lean`: base symbols
- `AutomatedTheoryConstruction/Derived.lean`: accumulated verified theorems plus AI-friendly aliases
- `AutomatedTheoryConstruction/Scratch.lean`: temporary generated verification file
- `data/open_problems.jsonl`: open problems
- `data/solved_problems.jsonl`: verified solved problems
- `data/counterexamples.jsonl`: verified counterexamples
- `scripts/run_loop.py`: orchestrator loop
- `scripts/state_update.py`: deterministic state transition logic
- `scripts/lean_verify.py`: Lean verification wrapper
- `scripts/append_derived.py`: append theorem into `Derived.lean`
- `prompts/prover_simple.md`: prover prompt used by the loop worker
- `prompts/formalizer_simple.md`: initial Lean formalization prompt
- `prompts/new_problem_expander.md`: follow-up problem generation prompt
- `.codex/skills/prover-interface/SKILL.md`: prover I/O contract

## Requirements

- Lean toolchain (see `lean-toolchain`)
- Lake + Mathlib dependencies
- Python environment
- `uv` for Python script execution

## Required Tools

To use the workflow in this repository, you will need the following tools.

* Codex CLI
* lean-lsp-mcp  
  [https://github.com/oOo0oOo/lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp)

Install `lean-lsp-mcp` and configure it so that Codex can access the Lean Language Server.

## Setup

1. Build Lean project:

```bash
lake build
```

2. Confirm Scratch verification path works:

```bash
lake env lean AutomatedTheoryConstruction/Scratch.lean
```

## Basic Usage

To define the base theory, edit `AutomatedTheoryConstruction/Theory.lean` and put your symbols, structures, and axioms there.

Then add a few seed statements to `theories/semigroup_like_01/seeds.jsonl`. These are the initial theorem candidates that the loop uses as starting points for theory development.

At startup, the loop initializes open problems from this `seeds.jsonl` file by default.

## Run: Loop Mode (default)

Uses a worker command invoked by the orchestrator (`scripts/run_loop.py`).

Required environment variables:

- `ATC_WORKER_COMMAND` (example: your codex worker executable)
- Optional: `ATC_WORKER_TIMEOUT` sets the outer worker subprocess timeout when `--worker-timeout` is not passed
- Optional: `ATC_FORMALIZE_WORKER_COMMAND` / `ATC_FORMALIZE_WORKER_TIMEOUT` override only the `formalize` task
- Optional: `ATC_REPAIR_WORKER_COMMAND` / `ATC_REPAIR_WORKER_TIMEOUT` override only the `repair` task

Timeout precedence:

- `--worker-timeout`
- `ATC_WORKER_TIMEOUT`
- default `180`

Task-specific overrides:

- `formalize`: `--formalize-worker-command` / `ATC_FORMALIZE_WORKER_COMMAND`, `--formalize-worker-timeout` / `ATC_FORMALIZE_WORKER_TIMEOUT`
- `repair`: `--repair-worker-command` / `ATC_REPAIR_WORKER_COMMAND`, `--repair-worker-timeout` / `ATC_REPAIR_WORKER_TIMEOUT`
- If task-specific values are unset, the loop falls back to the shared worker command/timeout above.
- `--repair-prompt-file` is optional; when omitted, `repair` reuses `--formalizer-prompt-file`.

Worker protocol (stdin -> stdout JSON):

- Request envelope keys: `task_type`, `system_prompt`, `payload`, `metadata`
- Response envelope keys: `result_payload`, `worker_meta`, `error`
- `worker_meta` may include `raw_model_output`, the full model-output text for that worker call
- `error` must be null/empty on success
- Supported `task_type` values: `prover`, `formalize`, `repair`, `expand`

For `scripts/codex_worker.py`, `ATC_WORKER_TIMEOUT` also bounds the inner Codex invocation unless `ATC_CODEX_TIMEOUT` is set explicitly.

During loop execution, each prover attempt also writes a reusable natural-language note:

- `data/proof_notes/<problem_id>.md`: statement, proof sketch, and counterexample intuition

Recommended Codex worker invocation:

```bash
ATC_WORKER_COMMAND="uv run scripts/codex_worker.py" \
ATC_CODEX_TIMEOUT=390 \
uv run scripts/run_loop.py --enable-worker --worker-timeout 420
```

Equivalent env-based timeout configuration:

```bash
ATC_WORKER_COMMAND="uv run scripts/codex_worker.py" \
ATC_WORKER_TIMEOUT=420 \
ATC_CODEX_TIMEOUT=390 \
uv run scripts/run_loop.py --enable-worker
```

Use a different solver only for formalization and repair:

```bash
ATC_WORKER_COMMAND="uv run scripts/codex_worker.py" \
ATC_WORKER_TIMEOUT=420 \
ATC_FORMALIZE_WORKER_COMMAND="python external_formalizer.py" \
ATC_FORMALIZE_WORKER_TIMEOUT=300 \
ATC_REPAIR_WORKER_COMMAND="python external_formalizer.py" \
ATC_REPAIR_WORKER_TIMEOUT=180 \
uv run scripts/run_loop.py --enable-worker
```

**Resume** (skip re-initialization):

```bash
ATC_WORKER_COMMAND="uv run scripts/codex_worker.py" \
ATC_WORKER_TIMEOUT=420 \
ATC_CODEX_TIMEOUT=390 \
uv run scripts/run_loop.py --enable-worker --no-initialize-on-start
```

## Data Format (JSONL)

Open problem example:

```json
{"id":"op_000001","stmt":"∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, (x * y) * z = x * (y * z)","src":"seed"}
```

Solved problem example:

```json
{"id":"op_000001","stmt":"∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, (x * y) * z = x * (y * z)","thm":"thm_op_000001"}
```

Counterexample example:

```json
{"id":"op_000002","stmt":"∀ {α : Type u} [SemigroupLike01 α], ∀ x y : α, x * y = y * x"}
```

## Notes on Formalization Policy

- Existing formalization workflow under `.codex` is intentionally preserved.
- Prover trial-and-error is delegated to Codex CLI interaction inside the worker.
- Natural-language prover sketches are persisted as markdown and reused in formalize/repair flow.
- Same-problem formalization history is persisted in `data/formalization_memory.json` and reused by repair/expansion.
- Expansion also receives `current_iteration_full_logs`, which contains the current iteration's full prover/formalize/repair model outputs in memory only.
- If a statement is not formalizable to Lean, the problem remains in `open`.

## License

This repository is licensed under the MIT License. See `LICENSE`.

## Reference

* Xin et al. (2025). *BFS-Prover-V2*.

## Acknowledgements

The prompting strategy for solving Lean problems was partially inspired by a private repository (kmd710/lean4-codex-skills).
This does not affect the theory construction framework itself, which is independently developed.
