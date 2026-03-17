# Codex / Lean Proof Workflow

This repository uses Lean 4 + Mathlib for formalization of results in quantum information and trace inequalities.

This `AGENTS.md` file is the authoritative runtime instruction set for this repository. If a starter template or external guidance differs from this file, follow this file for work in this repository.

Main entry points include:

- `Quantum.lean`
- `Quantum/QuantumEntropy/`
- `Quantum/QuantumMechanics/`
- `Quantum/TraceInequality/`
- `.codex/`: repository-local workflow and skill definitions

Use repository-local workflow and skill files under `.codex/` as supporting instructions, with this file as the primary source of truth.

## Equational Loop Addendum (picker/prover integration)

This repository also runs a minimal equational-theory loop around three roles:

- `picker`: chooses one open problem id
- `prover`: attempts the problem and proposes at most two new problems
- Lean formalization/verification: reuses the existing Lean workflow in this file

This addendum extends orchestration behavior only. It does not replace the Lean proof workflow below.

### Responsibility boundary

- LLM responsibility:
  - `picker` output: choose exactly one problem id
  - `prover` output: `proof | counterexample | stuck` with optional texts and 0-2 new problems
- Script responsibility (deterministic):
  - JSONL read/write
  - id allocation
  - duplicate filtering
  - state transitions (`open`/`solved`/`counterexample`)
  - appending verified theorems to `Derived.lean`

Do not move transaction/state-update decisions into prompts.

### Formalization boundary (preserve existing operation)

- Keep existing Lean formalization operation from this AGENTS file and repo skills (`lean-rule`, `mathlib-usage`).
- Do not introduce a separate heavy formalizer workflow for picker/prover integration.
- If a natural-language statement cannot be formalized to Lean, treat it as rejected formalization and keep it in `open` with incremented attempts (`n`).

### Module contract (Theory / Derived / Scratch)

- `AutomatedTheoryConstruction/Theory.lean`: base symbols/axiom interface
- `AutomatedTheoryConstruction/Derived.lean`: verified theorem accumulation target
- `AutomatedTheoryConstruction/Scratch.lean`: temporary generated verification file

Expected imports for generated verification code:

- `import AutomatedTheoryConstruction.Theory`
- `import AutomatedTheoryConstruction.Derived`

Verification path remains:

- `lake env lean AutomatedTheoryConstruction/Scratch.lean`

## Dialogue Policy (minimize human intervention)

- Provide a **single proposal** (including code edits and command plans); do not list alternatives that require user choice.
- Default to English unless the user clearly requests another language.
- Do not prepend model names or version names to normal replies.
- Do not ask for routine confirmation.
- If a decision can be made from local repository context, the current file, diagnostics, or nearby code/search results, make the decision and continue.
- Ask questions only when execution is impossible, safety is unclear, or a material design choice cannot be resolved from local context.
- Treat user questions as a last resort, not a normal step in the workflow.
- If a safe default exists, use it and continue without asking.
- Treat intermediate progress reports as inline status only, not as a stopping point or an implicit request for permission to continue.
- Continue autonomously while safe next actions remain; do not stop merely because one approach failed.
- If one approach stalls, re-search, re-plan, isolate the hotspot, or switch to another safe local step before considering a user question.
- Default when unsure: smallest and local change, keep existing API, avoid new dependencies, place new code under `Quantum/TraceInequality/`.
- Execute commands/edits immediately when they are necessary and safe; avoid waiting for confirmation for routine steps (exclude dangerous operations).
- Keep replies concise and action-oriented.

## Standard proof workflow

1. Read the target `.lean` theorem and any referenced `.md` (natural-language proof/notes) if present.
2. Plan first: outline a high-level strategy and split into `have` chains or small lemmas.
   - Planning is preparatory, not a terminal deliverable, unless the user explicitly asked for planning only.
   - Do not stop after describing the plan if implementation can continue safely.
3. For Lean formalization and substantial proof repair, use a visible skeleton-first workflow by default: first place many small `have ... := by sorry` steps in the file so the main dependency chain type-checks.
  - Treat the skeleton as a user-visible working state, not as a private planning note.
  - Only skip the skeleton when the proof closes immediately with a tiny local argument.
4. Work in two phases:
  - Phase 1: make the theorem body type-check with a small `have ... := by sorry` skeleton that exposes the dependency order.
  - Phase 2: fill the skeleton from the top until all `sorry`s are removed.
5. Error-driven iteration:
  - Fill the skeleton from the top, keeping each `have` small and easy to discharge.
  - Run `lake env lean <file>` to type-check before each new local proof step.
  - Fix exactly the topmost error with minimal edits.
  - After each error-level fix, immediately run `lake env lean <file>` again before making another speculative edit.
  - Do not batch several guessed fixes together before re-checking; prefer `one error fixed -> one fresh Lean run -> inspect the new top error`.
  - In Phase 1 and early Phase 2, treat non-semantic lint/style warnings as non-blocking when they do not obstruct proof progress.
    - Deferred warnings include pure style/formatting issues such as `longLine`, and proof-script cleanup warnings such as `unusedSimpArgs` / `unnecessarySimpa`.
    - Prioritize type errors, unsolved goals, elaboration problems, and heartbeat failures first.
  - If a local proof fragment hits a heartbeat error, isolate that fragment, temporarily revert just that fragment to `by sorry` if needed, continue the surrounding skeleton, and return later with a smaller local target.
  - Repeat until clean.
   - Intermediate status notes are allowed, but they do not replace continued execution when a safe next step is already clear.
6. Finish:
  - Phase 1 is complete when the intended dependency chain is present in the file and type-checks with temporary `sorry`s.
  - In Lean proof implementation or substantial proof repair, do not stop, wait for the user, or send a progress-only reply while compile errors, unsolved goals, elaboration failures, or relevant `sorry`s remain in the current target Lean file.
  - Before stopping, run `lake env lean <file>` on the current target Lean file and resolve the reported proof/type/elaboration errors first.
  - In Lean proof implementation or substantial proof repair, do not stop, wait for the user, or send a progress-only reply while any relevant `sorry` remains.
  - Before stopping, run `rg -n '\bsorry\b'` on the current target Lean file; extend the check to changed Lean files when the proof work spans more than that file.
  - If that search still finds a remaining proof `sorry`, continue from the easiest remaining one rather than stopping.
  - Phase 2 is complete when all relevant `sorry`s are removed, deferred non-semantic lint cleanup has been handled or intentionally localized, `lake env lean` succeeds again, and diffs stay minimal and local.

## Proof style

- Keep each `have` small (aim for 1–5 lines to fill).
- Use the skeleton-first workflow as the default for theorem formalization and substantial proof repair; reserve direct proofs for tiny local arguments.
- For subgoals, prefer local rewrites `rw` / `simpa` / `simp only` / `simp_rw` over `simp [*]` or large AC/definition explosions.
- Use `fun_prop` / `measurability` for function regularity, `positivity` / `finiteness` for sign/finitedness, `ring_nf` for commutative rings, and isolate `field_simp` in small helper lemmas.
- Always write multiplication `*` and powers `^` explicitly.
- Keep imports minimal; `import Mathlib` or `import Mathlib.*` is allowed when convenient.

## Mathlib usage and search

- Search with `rg -n "<keyword>" .lake/packages/mathlib/Mathlib`.
- Look for existing lemmas before writing new ones.
- Do not invent lemma names; verify existence before use.

## Common commands

- Type-check a file: `lake env lean path/to/File.lean`
- Build the whole project: `lake build`
- Repo search: `rg -n "<pattern>" .`
- If Python is needed, run via `uv run ...` (avoid raw `python` / `python3`). Lean tools (`lake ...`) are exempt.

## First-time setup (mathlib cache)

If cache fetch fails after `lake update` due to toolchain mismatch, align to mathlib:

- `cp .lake/packages/mathlib/lean-toolchain ./lean-toolchain`
- `lake exe cache get`
- `lake build`

## Safety and operations

- Run networked commands only when the user explicitly asks.
- Do not touch unrelated areas; keep edits minimal and purpose-bound.
- Do not `git commit` unless requested.
- No tab characters; use spaces for indent.
- Do not use `git restore`; use `git diff` / `git show` to revert minimally.
- Only adjust `maxHeartbeats` when errors mention it:
  - A heartbeat error should first trigger structural simplification: split declarations, isolate helper lemmas, shrink `simp`/`rw` scope, and reduce instance search.
  - If used, scope with `set_option maxHeartbeats <n> in` and leave a reason on the same or previous line.
  - Before raising heartbeats, try splitting declarations, `simp only`, small lemmas, and reducing instance search.

## Skills (.codex/skills/) index

Repo-local skills (rules/checklists) are under `.codex/skills/`:

- `lean-rule`: Lean proof/implementation rules (plan → skeleton → iterate → finish)
- `mathlib-usage`: Mathlib usage principles (import/search/existence check)
- `lean-review-refactor-policy`: review-safe non-semantic refactor policy
- `picker-interface`: picker I/O contract for equational loop selection
- `prover-interface`: prover I/O contract for equational loop attempts

Use these as supporting guidance under the authority of this `AGENTS.md`.

## Repo-local helper scripts

- `./.codex/scripts/codex-notify`: launches Codex CLI with a macOS idle notification wrapper
- For `sorry`-elimination workflows, the closest automation point is an outer wrapper/orchestrator that repeats a `rg -n '\bsorry\b'` check and reinvokes a continuation step until no relevant proof `sorry` remains; treat this as outer-session orchestration, not as a hook.
- See `./.codex/README.md` for setup and tuning options

## TraceInequality notes

- Place main implementations/proofs under `Quantum/TraceInequality/`.
- Prefer refactors that keep existing definitions/theorem statements unchanged; if changing them, state the intent.
- Split large lemmas into small helpers and keep naming within the `TraceInequality` namespace.
