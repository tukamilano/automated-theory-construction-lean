# Automated Theory Construction (Minimal Prototype)

This repository contains a minimal prototype for iterative theory growth on equational-style problems.

The current loop is:

1. Pick one open problem
2. Attempt proof / counterexample / stuck
3. Formalize and verify in Lean
4. Update state files
5. Reuse verified theorems from `Derived.lean`

## Current Scope

Implemented now:

- Lean module scaffold: `Theory.lean`, `Derived.lean`, `Scratch.lean`
- Data/state files: open / solved / counterexamples (JSONL)
- Deterministic state updates with atomic JSONL writes
- External configurable `max_attempts`
- Reject-and-keep-open behavior for unformalizable natural-language statements
- Picker/prover interface contracts in `.codex/skills`

Not implemented yet:

- Full LLM wiring for production picker/prover calls
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

## Run One Iteration (Mock Path)

Basic stuck-path dry run:

```bash
uv run scripts/run_loop.py \
  --skip-verify \
  --mock-result stuck \
  --mock-new-problem "Investigate right cancellation relation"
```

## Run One Iteration (JSON Contract Path)

Pass picker/prover outputs as JSON (useful when integrating external agent calls):

```bash
uv run scripts/run_loop.py \
  --skip-verify \
  --picker-output-json '{"selected_problem_id":"op_000001"}' \
  --prover-output-json '{"problem_id":"op_000001","result":"stuck","proof_text":"","counterexample_text":"","new_problems":["New helper candidate"]}'
```

## Run One Iteration (Live LLM Path)

This path uses an OpenAI-compatible Chat Completions endpoint.

Required environment variables:

- `ATC_LLM_API_KEY`
- Optional: `ATC_LLM_BASE_URL` (default: `https://api.openai.com/v1`)
- Optional: `ATC_LLM_MODEL` (default: `gpt-4.1-mini`)

Example:

```bash
ATC_LLM_API_KEY="<your_key>" \
uv run scripts/run_loop.py \
  --enable-llm \
  --skip-verify
```

Notes:

- Picker/prover prompts are loaded from `prompts/picker.md` and `prompts/prover.md`.
- You can override paths with `--picker-prompt-file` and `--prover-prompt-file`.
- You can override endpoint/model with CLI flags or environment variables.

## Max Attempts Configuration

Priority order:

1. CLI: `--max-attempts`
2. Environment variable: `ATC_MAX_ATTEMPTS`
3. Config file: `config/defaults.json`
4. Fallback default: `5`

Example:

```bash
ATC_MAX_ATTEMPTS=8 uv run scripts/run_loop.py --skip-verify --mock-result stuck
```

## Data Format (JSONL)

Open problem example:

```json
{"id":"op_000001","stmt":"forall x y z, op (op x y) z = op x (op y z)","src":"seed","n":0}
```

Solved problem example:

```json
{"id":"op_000001","stmt":"forall x y z, op (op x y) z = op x (op y z)","thm":"thm_op_000001"}
```

Counterexample example:

```json
{"id":"op_000010","stmt":"forall x y, op x y = op y x"}
```

## Notes on Formalization Policy

- Existing formalization workflow under `.codex` is intentionally preserved.
- Picker/prover were added as interface contracts, not as replacements for Lean proof workflow.
- If a statement is not formalizable to Lean, the problem remains in `open` and its attempt count is incremented.

## Next Recommended Steps

1. Replace mock picker/prover path with actual LLM calls returning contract-compliant JSON
2. Add structured JSON error outputs (instead of plain tracebacks) in `run_loop.py`
3. Add lightweight execution logs for debugging and reproducibility

## 参考文献

* Xin et al. (2025). *BFS-Prover-V2*.
* [kmd710/lean4-codex-skills](https://github.com/kmd710/lean4-codex-skills)
