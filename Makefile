SHELL := /bin/sh

LAKE ?= lake
PYTHON ?= uv run python
ATC ?= $(PYTHON) scripts/atc_cli.py

THEORY_FILE ?= AutomatedTheoryConstruction/Theory.lean
DERIVED_FILE ?= AutomatedTheoryConstruction/Derived.lean
SCRATCH_FILE ?= AutomatedTheoryConstruction/Scratch.lean
SEEDS_FILE ?= AutomatedTheoryConstruction/seeds.jsonl
PREVIEW_FILE ?= AutomatedTheoryConstruction/Derived.refactored.preview.lean
REVIEWED_FILE ?= AutomatedTheoryConstruction/Derived.refactored.reviewed.lean
TRY_AT_EACH_STEP_RAW_OUTPUT_FILE ?= AutomatedTheoryConstruction/Derived.tryAtEachStep.json
TRY_AT_EACH_STEP_APPLY_REPORT_FILE ?= AutomatedTheoryConstruction/Derived.tryAtEachStep.apply_report.json
DEPS_FILE ?= data/derived-deps.json
DERIVED_CHUNK_PLAN_FILE ?= data/derived-chunk-plan.json
GENERATED_ROOT ?= AutomatedTheoryConstruction/Generated
GENERATED_MANIFEST_FILE ?= $(GENERATED_ROOT)/Manifest.lean
GENERATED_CATALOG_FILE ?= $(GENERATED_ROOT)/catalog.json
GENERATED_LOCAL_MANIFEST_VERIFY_TIMEOUT ?= 300
SNAPSHOT_ROOT ?= snapshots

WORKER_COMMAND ?= uv run scripts/codex_worker.py
WORKER_TIMEOUT ?= 420
CODEX_TIMEOUT ?= 390

SEED_ARGS ?=
LOOP_ARGS ?=
CYCLE_ARGS ?=
PIPELINE_ARGS ?=
MAIN_THEOREM_ARGS ?=
REWRITE_ARGS ?=
REVIEW_ARGS ?=
MATERIALIZE_ARGS ?=
GENERATED_LOCAL_ARGS ?=

.PHONY: help build check check-theory check-derived check-scratch smoke seed loop loop-continue cycle pipeline main-theorem rewrite review refactor-to-generated

help:
	@printf '%s\n' \
		'Available targets:' \
		'  make build         - lake build' \
		'  make check         - check Theory, Derived, Scratch' \
		'  make check-theory  - lake env lean $(THEORY_FILE)' \
		'  make check-derived - lake env lean $(DERIVED_FILE)' \
		'  make check-scratch - lake env lean $(SCRATCH_FILE)' \
		'  make smoke         - isolated mock-worker smoke test in a temp repo copy' \
		'  make seed          - generate seeds.jsonl via scripts/atc_cli.py seed' \
		'  make loop          - run the default worker loop via scripts/atc_cli.py loop' \
		'  make loop-continue - same as loop, but keep current runtime state' \
		'  make cycle         - run one cycle: loop -> main theorem -> refactor -> snapshot' \
		'  make pipeline      - run seed -> loop -> rewrite -> review via scripts/atc_cli.py pipeline' \
		'  make main-theorem  - run a one-shot main theorem session via scripts/atc_cli.py main-theorem' \
		'  make rewrite       - run scripts/atc_cli.py rewrite' \
		'  make review        - run scripts/atc_cli.py review' \
		'  make refactor-to-generated - run pass1.5 -> pass2 -> split -> local pass1.2 -> local pass1.3' \
		'' \
		'Common overrides:' \
		'  WORKER_COMMAND="uv run scripts/mock_worker.py"' \
		'  WORKER_TIMEOUT=600 CODEX_TIMEOUT=540' \
		'  THEORY_FILE=... DERIVED_FILE=... SCRATCH_FILE=...' \
		'  THEORY_FILE should point to the Theory.lean entry module' \
		'  SEED_ARGS="--context-file path/to/context.tex --seed-count 4"' \
		'  LOOP_ARGS="--max-iterations 40"' \
		'  CYCLE_ARGS="--cycle-iterations 20 --snapshot-root snapshots"' \
		'  MAIN_THEOREM_ARGS="--skip-verify --current-iteration 0"' \
		'  PIPELINE_ARGS="--context-file path/to/context.tex --max-iterations 40"'

build:
	$(LAKE) build

check: check-theory check-derived check-scratch

check-theory:
	$(LAKE) env lean $(THEORY_FILE)

check-derived:
	$(LAKE) env lean $(DERIVED_FILE)

check-scratch:
	$(LAKE) env lean $(SCRATCH_FILE)

smoke:
	python3 tests/smoke_test.py

seed:
	$(ATC) seed \
		--theory-file $(THEORY_FILE) \
		--derived-file $(DERIVED_FILE) \
		--seeds-file $(SEEDS_FILE) \
		$(SEED_ARGS)

loop:
	$(ATC) loop \
		--worker-command "$(WORKER_COMMAND)" \
		--worker-timeout "$(WORKER_TIMEOUT)" \
		--codex-timeout "$(CODEX_TIMEOUT)" \
		$(LOOP_ARGS)

loop-continue:
	$(ATC) loop \
		--worker-command "$(WORKER_COMMAND)" \
		--worker-timeout "$(WORKER_TIMEOUT)" \
		--codex-timeout "$(CODEX_TIMEOUT)" \
		--no-initialize-on-start \
		$(LOOP_ARGS)

cycle:
	$(ATC) cycle \
		--worker-command "$(WORKER_COMMAND)" \
		--worker-timeout "$(WORKER_TIMEOUT)" \
		--codex-timeout "$(CODEX_TIMEOUT)" \
		--snapshot-root $(SNAPSHOT_ROOT) \
		$(CYCLE_ARGS)

pipeline:
	$(ATC) pipeline \
		--worker-command "$(WORKER_COMMAND)" \
		--worker-timeout "$(WORKER_TIMEOUT)" \
		--codex-timeout "$(CODEX_TIMEOUT)" \
		--preview-file $(PREVIEW_FILE) \
		--review-output-file $(REVIEWED_FILE) \
		$(PIPELINE_ARGS)

main-theorem:
	$(ATC) main-theorem \
		--theory-file $(THEORY_FILE) \
		--derived-file $(DERIVED_FILE) \
		--scratch-file $(SCRATCH_FILE) \
		$(MAIN_THEOREM_ARGS)

rewrite:
	$(ATC) rewrite \
		--input-file $(PREVIEW_FILE) \
		--output-file $(PREVIEW_FILE) \
		--raw-output-file $(TRY_AT_EACH_STEP_RAW_OUTPUT_FILE) \
		--apply-report-file $(TRY_AT_EACH_STEP_APPLY_REPORT_FILE) \
		$(REWRITE_ARGS)

review:
	$(ATC) review \
		--input-file $(PREVIEW_FILE) \
		--output-file $(REVIEWED_FILE) \
		$(REVIEW_ARGS)

refactor-to-generated:
	cp $(DERIVED_FILE) $(PREVIEW_FILE)
	$(ATC) rewrite \
		--input-file $(PREVIEW_FILE) \
		--output-file $(PREVIEW_FILE) \
		--raw-output-file $(TRY_AT_EACH_STEP_RAW_OUTPUT_FILE) \
		--apply-report-file $(TRY_AT_EACH_STEP_APPLY_REPORT_FILE) \
		$(REWRITE_ARGS)
	$(ATC) review \
		--input-file $(PREVIEW_FILE) \
		--output-file $(REVIEWED_FILE) \
		$(REVIEW_ARGS)
	cp $(REVIEWED_FILE) $(DERIVED_FILE)
	$(ATC) materialize-generated \
		--derived-file $(DERIVED_FILE) \
		--deps-file $(DEPS_FILE) \
		--generated-root $(GENERATED_ROOT) \
		--manifest-file $(GENERATED_MANIFEST_FILE) \
		--catalog-file $(GENERATED_CATALOG_FILE) \
		--plan-file $(DERIVED_CHUNK_PLAN_FILE) \
		$(MATERIALIZE_ARGS)
	$(PYTHON) scripts/refactor/run_generated_local_passes.py \
		--generated-root $(GENERATED_ROOT) \
		--theory-file $(THEORY_FILE) \
		--worker-command "$(WORKER_COMMAND)" \
		--worker-timeout $(WORKER_TIMEOUT) \
		--manifest-verify-timeout $(GENERATED_LOCAL_MANIFEST_VERIFY_TIMEOUT) \
		$(GENERATED_LOCAL_ARGS)
