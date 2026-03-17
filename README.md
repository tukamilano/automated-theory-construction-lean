# Automated Theory Construction (Minimal Prototype)

This repository contains a minimal prototype for iterative theory growth on equational-style problems.

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
- Deterministic state updates with atomic JSONL writes
- Auto-initialize from seeds on startup (default on)
- LLM wiring via OpenAI-compatible Chat Completions (e.g. Groq)
- Picker/prover interface contracts in `.codex/skills`
- Single-shot proof mode (`--mode single-shot`)

Not implemented yet:

- Heavy repair loops
- Graph/candidate-queue/provenance infrastructure

## Repository Layout

- `AutomatedTheoryConstruction/Theory.lean`: base symbols
- `AutomatedTheoryConstruction/Derived.lean`: accumulated verified theorems
- `AutomatedTheoryConstruction/Scratch.lean`: temporary generated verification file
- `data/open_problems.jsonl`: open problems
- `data/solved_problems.jsonl`: verified solved problems
- `data/counterexamples.jsonl`: verified counterexamples
- `scripts/run_loop.py`: one-iteration orchestrator
- `scripts/state_update.py`: deterministic state transition logic
- `scripts/lean_verify.py`: Lean verification wrapper
- `scripts/append_derived.py`: append theorem into `Derived.lean`
- `prompts/picker.md`: picker prompt contract
- `prompts/prover.md`: prover prompt contract
- `.codex/skills/picker-interface/SKILL.md`: picker I/O contract
- `.codex/skills/prover-interface/SKILL.md`: prover I/O contract

## Requirements

- Lean toolchain (see `lean-toolchain`)
- Lake + Mathlib dependencies
- Python environment
- `uv` for Python script execution

## Setup

1. Build Lean project:

```bash
lake build
```

2. Confirm Scratch verification path works:

```bash
lake env lean AutomatedTheoryConstruction/Scratch.lean
```

## Run: Loop Mode (default)

Uses an OpenAI-compatible Chat Completions endpoint.

Required environment variables:

- `ATC_LLM_API_KEY`
- Optional: `ATC_LLM_BASE_URL` (default: `https://api.openai.com/v1`)
- Optional: `ATC_LLM_MODEL` (default: `gpt-4.1-mini`)

**Fresh start** (initializes from seeds):

```bash
ATC_LLM_API_KEY="<your_key>" \
uv run scripts/run_loop.py --enable-llm
```

**Resume** (skip re-initialization):

```bash
ATC_LLM_API_KEY="<your_key>" \
uv run scripts/run_loop.py --enable-llm --no-initialize-on-start
```

**Using Groq** (recommended free-tier option):

```bash
ATC_LLM_API_KEY="<groq_key>" \
ATC_LLM_BASE_URL=https://api.groq.com/openai/v1 \
ATC_LLM_MODEL=llama-3.3-70b-versatile \
uv run scripts/run_loop.py --enable-llm
```

## Run: Single-Shot Proof Mode

Directly attempt to prove one statement without updating any state files:

```bash
ATC_LLM_API_KEY="<your_key>" \
uv run scripts/run_loop.py \
  --mode single-shot \
  --enable-llm \
  --single-shot-stmt "∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, op (op x y) z = op x (op y z)"
```

Note: `single-shot` mode does not update `open/solved/counterexamples` JSONL files.

## Data Format (JSONL)

Open problem example:

```json
{"id":"op_000001","stmt":"∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, op (op x y) z = op x (op y z)","src":"seed","n":0}
```

Solved problem example:

```json
{"id":"op_000001","stmt":"∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, op (op x y) z = op x (op y z)","thm":"thm_op_000001"}
```

Counterexample example:

```json
{"id":"op_000010","stmt":"∀ {α : Type u} [SemigroupLike01 α], ∀ x y : α, op x y = op y x"}
```

## Notes on Formalization Policy

- Existing formalization workflow under `.codex` is intentionally preserved.
- Picker/prover were added as interface contracts, not as replacements for Lean proof workflow.
- If a statement is not formalizable to Lean, the problem remains in `open` and its attempt count is incremented.

## Next Recommended Steps

1. Achieve a first successful proof in single-shot mode
2. Verify that the proof round-trips through Lean (`--skip-verify` off)
3. Begin exploration loop (loop mode with multiple iterations)

## 参考文献

* Xin et al. (2025). *BFS-Prover-V2*.
* [kmd710/lean4-codex-skills](https://github.com/kmd710/lean4-codex-skills)
