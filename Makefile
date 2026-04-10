SHELL := /bin/sh

LAKE ?= lake
PYTHON ?= uv run python
ATC ?= $(PYTHON) scripts/atc_cli.py

THEORY_FILE ?= AutomatedTheoryConstruction/Theory.lean
DERIVED_FILE ?= AutomatedTheoryConstruction/Derived.lean
SCRATCH_FILE ?= AutomatedTheoryConstruction/Scratch.lean
SEEDS_FILE ?= AutomatedTheoryConstruction/seeds.jsonl
PREVIEW_FILE ?= AutomatedTheoryConstruction/Derived.refactored.preview.lean
COMPRESSION_PLAN_FILE ?= AutomatedTheoryConstruction/Derived.compression.plan.json
COMPRESSION_REPORT_FILE ?= AutomatedTheoryConstruction/Derived.compression.report.json
COMPRESSION_PROGRESS_LOG_FILE ?= AutomatedTheoryConstruction/Derived.compression.executor.log.jsonl
REVIEWED_FILE ?= AutomatedTheoryConstruction/Derived.refactored.reviewed.lean
TRY_AT_EACH_STEP_RAW_OUTPUT_FILE ?= AutomatedTheoryConstruction/Derived.tryAtEachStep.json
TRY_AT_EACH_STEP_APPLY_REPORT_FILE ?= AutomatedTheoryConstruction/Derived.tryAtEachStep.apply_report.json

WORKER_COMMAND ?= uv run scripts/codex_worker.py
WORKER_TIMEOUT ?= 420
CODEX_TIMEOUT ?= 390
MAIN_THEOREM_INTERVAL ?= 10
MAIN_THEOREM_FORMALIZE_WORKER_TIMEOUT ?= 900
MAIN_THEOREM_REPAIR_WORKER_TIMEOUT ?= 600

SEED_ARGS ?=
LOOP_ARGS ?=
PIPELINE_ARGS ?=
REFACTOR_ARGS ?=
REWRITE_ARGS ?=
REVIEW_ARGS ?=

.PHONY: help build check check-theory check-derived check-scratch smoke seed loop loop-continue pipeline compress retarget rewrite review

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
		'  make pipeline      - run seed -> loop -> compress -> retarget -> rewrite -> review via scripts/atc_cli.py pipeline' \
		'  make compress      - run scripts/atc_cli.py compress' \
		'  make retarget      - run scripts/atc_cli.py retarget' \
		'  make rewrite       - run scripts/atc_cli.py rewrite' \
		'  make review        - run scripts/atc_cli.py review' \
		'' \
		'Common overrides:' \
		'  WORKER_COMMAND="uv run scripts/mock_worker.py"' \
		'  WORKER_TIMEOUT=600 CODEX_TIMEOUT=540' \
		'  MAIN_THEOREM_INTERVAL=10 MAIN_THEOREM_FORMALIZE_WORKER_TIMEOUT=900' \
		'  MAIN_THEOREM_REPAIR_WORKER_TIMEOUT=600' \
		'  THEORY_FILE=... DERIVED_FILE=... SCRATCH_FILE=...' \
		'  THEORY_FILE should point to the Theory.lean entry module' \
		'  SEED_ARGS="--context-file path/to/context.tex --seed-count 4"' \
		'  LOOP_ARGS="--max-iterations 40"' \
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
		--main-theorem-interval $(MAIN_THEOREM_INTERVAL) \
		--main-theorem-formalize-worker-timeout $(MAIN_THEOREM_FORMALIZE_WORKER_TIMEOUT) \
		--main-theorem-repair-worker-timeout $(MAIN_THEOREM_REPAIR_WORKER_TIMEOUT) \
		$(LOOP_ARGS)

loop-continue:
	$(ATC) loop \
		--worker-command "$(WORKER_COMMAND)" \
		--worker-timeout "$(WORKER_TIMEOUT)" \
		--codex-timeout "$(CODEX_TIMEOUT)" \
		--no-initialize-on-start \
		--main-theorem-interval $(MAIN_THEOREM_INTERVAL) \
		--main-theorem-formalize-worker-timeout $(MAIN_THEOREM_FORMALIZE_WORKER_TIMEOUT) \
		--main-theorem-repair-worker-timeout $(MAIN_THEOREM_REPAIR_WORKER_TIMEOUT) \
		$(LOOP_ARGS)

pipeline:
	$(ATC) pipeline \
		--worker-command "$(WORKER_COMMAND)" \
		--worker-timeout "$(WORKER_TIMEOUT)" \
		--codex-timeout "$(CODEX_TIMEOUT)" \
		--main-theorem-interval $(MAIN_THEOREM_INTERVAL) \
		--main-theorem-formalize-worker-timeout $(MAIN_THEOREM_FORMALIZE_WORKER_TIMEOUT) \
		--main-theorem-repair-worker-timeout $(MAIN_THEOREM_REPAIR_WORKER_TIMEOUT) \
		--preview-file $(PREVIEW_FILE) \
		--compression-plan-file $(COMPRESSION_PLAN_FILE) \
		--compression-report-file $(COMPRESSION_REPORT_FILE) \
		--compression-progress-log-file $(COMPRESSION_PROGRESS_LOG_FILE) \
		--review-output-file $(REVIEWED_FILE) \
		$(PIPELINE_ARGS)

compress:
	$(ATC) compress \
		--input-file $(PREVIEW_FILE) \
		--output-file $(PREVIEW_FILE) \
		--compression-plan-file $(COMPRESSION_PLAN_FILE) \
		--compression-report-file $(COMPRESSION_REPORT_FILE) \
		--compression-progress-log-file $(COMPRESSION_PROGRESS_LOG_FILE) \
		--worker-command "$(WORKER_COMMAND)" \
		--worker-timeout "$(WORKER_TIMEOUT)" \
		--refactor-codex-timeout "$(CODEX_TIMEOUT)" \
		$(REFACTOR_ARGS)

retarget:
	$(ATC) retarget \
		--input-file $(PREVIEW_FILE) \
		--output-file $(PREVIEW_FILE) \
		--worker-command "$(WORKER_COMMAND)" \
		--worker-timeout "$(WORKER_TIMEOUT)" \
		--refactor-codex-timeout "$(CODEX_TIMEOUT)" \
		$(REFACTOR_ARGS)

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
