# CLI / Config / Logging Design

## Status

Draft for contributor review.

This document is intended for people working on the repository, not as an
end-user guide. It explains the problem we are trying to solve, the design
being proposed, the tradeoffs behind it, and the migration path from the
 current runtime scripts.

## Summary

The repository currently has several operational scripts with overlapping but
inconsistent command-line interfaces, configuration rules, and logging styles.
The proposal in this document is to introduce:

- one shared CLI entrypoint
- one shared configuration resolution layer
- one shared logging model for both console output and persisted run artifacts

The goal is not to redesign the automated-theory-construction workflow itself.
The goal is to make the workflow easier to run, debug, extend, and review.

## Scope

This proposal covers the current single-theory runtime built around these
scripts:

- `scripts/run_loop.py`
- `scripts/run_pipeline.py`
- `scripts/generate_seeds_from_theory.py`
- `scripts/refactor_derived.py`
- `scripts/direct_refactor_derived.py`

This proposal does not try to solve generic multi-theory orchestration yet.

## Goals

- Keep the current workflows usable throughout the migration.
- Present one coherent CLI instead of several script-local CLIs.
- Make configuration precedence explicit and uniform.
- Separate human-facing progress logs from machine-facing structured logs.
- Make failed runs diagnosable from saved artifacts instead of source reading.

## Non-Goals

- Multi-theory runtime selection.
- Remote logging or log aggregation.
- Replacing JSONL runtime state with a database.
- Removing the `Makefile` in the first implementation phase.

## Why Change Anything

The current setup works, but operational behavior is spread across multiple
scripts. That creates a few recurring problems:

- different scripts expose similar concepts through different flags
- some runtime paths are fixed in code rather than coming from a shared config
- configuration is split across defaults, CLI flags, and environment variables
  without one resolver
- logging mixes human-readable status messages, ad hoc `print(...)` output, and
  structured dictionaries
- there is no standard run directory that captures what happened during one
  execution

None of these issues is fatal in isolation. Together, they make the runtime
harder to operate and harder to modify safely.

## Proposed Architecture

The proposal is to standardize three concerns behind shared modules:

- `scripts/atc_cli.py`
- `scripts/atc_config.py`
- `scripts/atc_logging.py`

Responsibilities:

- `atc_cli.py`
  - user-facing command structure
  - shared global flags
  - dispatch into existing runtime stages
- `atc_config.py`
  - load config file
  - read environment variables
  - merge CLI overrides
  - expose resolved typed settings
- `atc_logging.py`
  - console logging policy
  - structured event logging
  - run directory creation
  - summary and artifact persistence

The key design choice is incremental adoption. Existing scripts should not be
replaced all at once. Instead, they should gradually depend on the shared
layers until the old script-local logic becomes thin enough to remove.

## CLI Design

### Primary Entry Point

Proposed top-level entrypoint:

```bash
uv run python scripts/atc_cli.py <subcommand> [options]
```

Target subcommands:

- `atc seed`
- `atc loop`
- `atc pipeline`
- `atc refactor`
- `atc review`
- `atc config show`

This does not require us to stop exposing the existing scripts directly. In the
short term, the existing scripts remain valid entrypoints. The new CLI becomes
the preferred user-facing interface, while older entrypoints remain as
compatibility paths.

### Shared Global Flags

The following flags should be available globally, or consistently available on
the subcommands where they make sense:

- `--config <path>`
- `--data-dir <path>`
- `--log-dir <path>`
- `--log-format <pretty|json>`
- `--log-level <debug|info|warning|error>`
- `--log-worker-raw`
- `--dry-run`

These are intentionally cross-cutting flags. They should not be redefined with
slightly different names from script to script.

### Subcommand Responsibilities

`seed`

- generate seeds from theory and optional context files
- optionally initialize runtime state
- sync generated seeds into `open_problems.jsonl`

Example:

```bash
uv run python scripts/atc_cli.py seed \
  --context-file materials/context.tex \
  --seed-count 4
```

`loop`

- initialize runtime state when requested
- run the main automated-theory-construction loop
- emit a run summary and saved logs

Example:

```bash
uv run python scripts/atc_cli.py loop \
  --enable-worker \
  --max-iterations 40
```

`pipeline`

- run seed generation
- run the main loop
- run the first refactor pass
- run the second review pass
- record the whole execution under a parent run id

Example:

```bash
uv run python scripts/atc_cli.py pipeline \
  --context-file materials/context.tex \
  --max-iterations 40
```

`config show`

- print the fully resolved configuration
- make configuration precedence visible
- help diagnose “why did this value win?” problems

Example:

```bash
uv run python scripts/atc_cli.py config show
```

## Configuration Design

### Configuration Precedence

The proposal is to use one explicit precedence rule everywhere:

1. CLI flags
2. environment variables
3. config file
4. hardcoded defaults

This matters because different scripts currently have slightly different
behavior. Once we document a single rule, configuration bugs become easier to
reason about and easier to test.

### Config File Format

Recommended filename:

- `atc.toml`

Optional tracked sample:

- `atc.example.toml`

TOML is a reasonable fit here because:

- it is readable enough for humans
- it is structured enough for nested settings
- Python can parse it with `tomllib`
- it avoids adding a dependency just to load configuration

### Config Structure

Proposed top-level sections:

- `[paths]`
- `[worker]`
- `[worker.tasks.prover]`
- `[worker.tasks.prover_statement]`
- `[worker.tasks.formalize]`
- `[worker.tasks.repair]`
- `[worker.tasks.prioritize_open_problems]`
- `[worker.tasks.refactor_derived]`
- `[runtime]`
- `[logging]`

Example:

```toml
[paths]
theory_file = "AutomatedTheoryConstruction/Theory.lean"
derived_file = "AutomatedTheoryConstruction/Derived.lean"
scratch_file = "AutomatedTheoryConstruction/Scratch.lean"
seeds_file = "AutomatedTheoryConstruction/seeds.jsonl"
data_dir = "data"
prompt_dir = "prompts"
log_dir = "data/runs"

[worker]
command = "uv run scripts/codex_worker.py"
timeout = 420
codex_timeout = 390

[worker.tasks.formalize]
timeout = 600

[worker.tasks.repair]
timeout = 600

[runtime]
initialize_on_start = true
open_problem_failure_threshold = 2
priority_refresh_theorem_interval = 5
main_theorem_interval = 10
main_theorem_verify_timeout = 600
main_theorem_formalization_retry_budget_sec = 3600

[logging]
console_level = "info"
console_format = "pretty"
persist_events = true
persist_summary = true
persist_worker_raw = false
```

### Typed Settings Model

The config loader should resolve raw values into explicit dataclasses rather
than leaving the rest of the code to parse untyped dictionaries.

Suggested types:

- `PathsConfig`
- `WorkerTaskConfig`
- `WorkerConfig`
- `RuntimeConfig`
- `LoggingConfig`
- `AppConfig`

`AppConfig` should be the boundary object that orchestrator code consumes.

This is mainly about maintainability. If a script needs to know where the
derived file lives or what timeout applies to a worker, it should ask a typed
config object, not re-run its own merge logic.

### Backward Compatibility With Environment Variables

The existing `ATC_*` variables should remain supported during migration.

Examples:

- `ATC_WORKER_COMMAND`
- `ATC_WORKER_TIMEOUT`
- `ATC_CODEX_TIMEOUT`
- `ATC_FORMALIZE_WORKER_TIMEOUT`
- `ATC_REPAIR_WORKER_TIMEOUT`

The recommendation is not to expand this surface unnecessarily. New
environment-variable names should only be added when they map cleanly onto the
shared config model.

### Path Resolution Rules

Path handling should be explicit and consistent:

- paths from the config file are resolved relative to the config file location
- paths passed on the CLI are resolved relative to the current working
  directory
- persisted summaries may store both the raw path string and the resolved path
  when that helps debugging

This avoids a class of bugs where a config works only when invoked from one
directory.

## Logging Design

### Logging Principles

The proposal separates logging into two outputs with different purposes:

- console logs for humans following a run live
- persisted logs for automation, debugging, and postmortem analysis

That separation is important because the current runtime sometimes tries to use
the same output channel for both.

### Run Directory Layout

Each run should get its own directory:

```text
data/runs/<run_id>/
```

Suggested contents:

- `events.jsonl`
- `summary.json`
- `config.resolved.json`
- `worker_outputs/`
- `artifacts/`

If a pipeline consists of multiple stages, those stages should be nested under
the same parent run:

```text
data/runs/<run_id>/
data/runs/<run_id>/stages/seed/
data/runs/<run_id>/stages/loop/
data/runs/<run_id>/stages/refactor/
data/runs/<run_id>/stages/review/
```

This layout gives us a stable place to look whenever a run fails or behaves
unexpectedly.

### Event Log Format

Persist one JSON object per line in `events.jsonl`.

Required fields:

- `ts`
- `run_id`
- `event`
- `level`
- `component`

Common optional fields:

- `stage`
- `iteration`
- `problem_id`
- `status`
- `duration_ms`
- `worker_task`
- `error`

Example:

```json
{"ts":"2026-03-28T11:02:14+09:00","run_id":"20260328-110214-loop","event":"phase_begin","level":"info","component":"run_loop","stage":"prover","iteration":3,"problem_id":"p17"}
{"ts":"2026-03-28T11:02:31+09:00","run_id":"20260328-110214-loop","event":"worker_timeout","level":"warning","component":"worker_client","worker_task":"formalize","iteration":3,"problem_id":"p17","duration_ms":180000}
```

The important thing here is stability. The event stream should be easy to parse
and should not depend on ad hoc `print(...)` formatting.

### Summary Format

`summary.json` should be a compact record of what happened, not a copy of the
whole event log.

Suggested fields:

- `run_id`
- `command`
- `status`
- `started_at`
- `finished_at`
- `duration_ms`
- `iterations_completed`
- `theorems_appended`
- `active_open_problem_count`
- `archived_problem_count`
- `output_files`

### Raw Worker Output Policy

Raw worker output is useful for debugging but expensive to keep by default.

Recommended default:

- console: never print full raw worker output
- summary: never inline full raw worker output
- persisted logs: save raw output only when `persist_worker_raw = true`

When raw outputs are saved, they should live in separate files rather than be
embedded into `events.jsonl`.

Suggested path:

```text
data/runs/<run_id>/worker_outputs/<iteration>_<task>_<problem_id>.txt
```

This keeps structured logs compact while still preserving deep debugging data
when explicitly requested.

### Console Logging Policy

Console output should stay short and easy to scan. Typical messages:

- run start
- phase begin
- phase result
- iteration result
- verification failure summary
- final summary

The general policy should be:

- use stderr for progress logs
- reserve stdout for programmatic output when a command is intentionally acting
  like a machine interface

For the unified CLI, human-readable console output should be the default.
`--log-format json` can remain available for tooling.

## Migration Plan

The migration should be staged. That reduces breakage risk and lets us verify
behavior incrementally.

### Phase 0: Freeze Interfaces

- document the current scripts and environment variables
- identify compatibility behavior we are not willing to break

### Phase 1: Shared Config And Logging

- add `scripts/atc_config.py`
- add `scripts/atc_logging.py`
- keep the current script-specific parsers
- move `scripts/run_loop.py` and `scripts/run_pipeline.py` onto the shared
  helpers

Expected result:

- current workflows still behave the same
- configuration logic becomes centralized
- runs gain a standard persisted log layout

### Phase 2: Unified CLI

- add `scripts/atc_cli.py`
- implement `seed`, `loop`, `pipeline`, `refactor`, `review`, `config show`
- keep old scripts as compatibility entrypoints

Expected result:

- one preferred CLI for users and contributors
- existing script-level entrypoints still work

### Phase 3: Compatibility Cleanup

- reduce duplicated parser logic
- align flag names
- route old flags through shared config mapping
- move fixed runtime defaults out of `scripts/run_loop.py`

### Phase 4: Makefile Simplification

- switch `Makefile` targets to call the unified CLI
- keep the user-facing target names unchanged

## Validation Plan

Minimum validation coverage should include:

- `seed --dry-run` resolves configuration correctly
- `loop` still runs with the mock worker
- `pipeline` writes stage-scoped logs under one parent run
- existing `make loop` behavior still works
- environment variables override config file values
- CLI flags override environment variables
- failure cases persist enough information to diagnose timeouts and Lean
  verification failures

Recommended automated checks:

- unit tests for config precedence
- unit tests for path resolution
- unit tests for run id generation
- snapshot-style tests for `config show`

## Recommended First Implementation Slice

If we want the smallest useful increment, the implementation order should be:

1. `scripts/atc_config.py`
2. `scripts/atc_logging.py`
3. migrate `scripts/run_loop.py`
4. migrate `scripts/run_pipeline.py`
5. add `scripts/atc_cli.py`
6. switch `Makefile` only after compatibility is confirmed

This sequence keeps the highest-risk behavioral changes late, after the shared
plumbing exists.

## Open Questions

The following points should be settled before we treat this design as final:

- Should `atc.toml` be checked in as the main config, or should only
  `atc.example.toml` be tracked?
- When raw worker output is enabled, should it be saved for every task or only
  on failure?
- Should the unified CLI default to human-readable console output or final JSON
  output?
- How long do we want to preserve environment-variable compatibility for
  per-task worker overrides?

## Decision Summary

If we adopt this proposal, we are choosing the following direction:

- one preferred CLI instead of multiple competing script-local interfaces
- one documented configuration precedence rule
- one run-scoped logging model
- incremental migration rather than a hard cutover

That is a modest architectural change, but it should lower the operational cost
of the repository substantially.
