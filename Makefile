SHELL := /bin/sh

LAKE ?= lake
PYTHON ?= uv run python
ATC ?= $(PYTHON) scripts/atc_cli.py
CONTINUE_CONFIG ?= configs/atc.continue.json
ATC_COMMON_ARGS ?=

THEORY_FILE ?= AutomatedTheoryConstruction/Theory.lean
DERIVED_FILE ?= AutomatedTheoryConstruction/Derived.lean
SCRATCH_FILE ?= AutomatedTheoryConstruction/Scratch.lean
SEEDS_FILE ?= AutomatedTheoryConstruction/seeds.jsonl
PREVIEW_FILE ?= AutomatedTheoryConstruction/Derived.refactored.preview.lean
ALPHA_DEDUPE_REPORT_FILE ?= AutomatedTheoryConstruction/Derived.alpha_dedupe.report.json
ALPHA_DEDUPE_EQUIVALENCE_MODE ?= defeq
REVIEWED_FILE ?= AutomatedTheoryConstruction/Derived.refactored.reviewed.lean
MATERIALIZE_DERIVED_FILE ?= $(DERIVED_FILE)
TRY_AT_EACH_STEP_RAW_OUTPUT_FILE ?= data/refactor/Derived.tryAtEachStep.json
TRY_AT_EACH_STEP_APPLY_REPORT_FILE ?= data/refactor/Derived.tryAtEachStep.apply_report.json
DEPS_FILE ?= data/refactor/derived-deps.json
DERIVED_CHUNK_PLAN_FILE ?= data/refactor/derived-chunk-plan.json
GENERATED_ROOT ?= AutomatedTheoryConstruction/Generated
GENERATED_MANIFEST_FILE ?= $(GENERATED_ROOT)/Manifest.lean
GENERATED_CATALOG_FILE ?= $(GENERATED_ROOT)/catalog.json
SNAPSHOT_ROOT ?= snapshots
REPORT_FILE ?=

WORKER_COMMAND ?= uv run scripts/codex_worker.py
WORKER_TIMEOUT ?= 420
CODEX_TIMEOUT ?= 390

SEED_ARGS ?=
LOOP_ARGS ?=
CYCLE_ARGS ?=
PIPELINE_ARGS ?=
PAPER_CLAIM_ARGS ?=
REWRITE_ARGS ?=
REVIEW_ARGS ?=
MATERIALIZE_ARGS ?=

.PHONY: help build check check-theory check-derived check-scratch smoke test seed seed-loop-refactor-to-generated loop loop-continue loop-refactor-to-generated loop-continue-refactor-to-generated cycle pipeline paper-claim theorem-dedupe alpha-dedupe rewrite review materialize-generated materialize-reviewed-generated refactor-to-generated research-agenda materials-cache materials-derive data-migrate-layout-dry-run data-migrate-layout

help:
	@printf '%s\n' \
		'Available targets:' \
		'  make build         - lake build' \
		'  make check         - check Theory, Derived, Scratch' \
		'  make check-theory  - lake env lean $(THEORY_FILE)' \
		'  make check-derived - lake env lean $(DERIVED_FILE)' \
		'  make check-scratch - lake env lean $(SCRATCH_FILE)' \
		'  make smoke         - isolated mock-worker smoke test in a temp repo copy' \
		'  make test          - run all tests under tests/*_test.py' \
		'  make seed          - generate seeds.jsonl via scripts/atc_cli.py seed' \
		'  make seed-loop-refactor-to-generated - run seed -> loop -> theorem-dedupe -> pass1.5 -> pass2 -> materialize generated' \
		'  make loop          - run the default worker loop via scripts/atc_cli.py loop' \
		'  make loop-continue - same as loop, but keep current runtime state' \
		'  make loop-refactor-to-generated - run loop -> theorem-dedupe -> pass1.5 -> pass2 -> materialize generated' \
		'  make loop-continue-refactor-to-generated - run loop-continue -> theorem-dedupe -> pass1.5 -> pass2 -> materialize generated using $(CONTINUE_CONFIG)' \
		'  make cycle         - run one cycle: loop -> paper claim -> refactor -> snapshot' \
		'  make pipeline      - run seed -> loop -> theorem-dedupe -> rewrite -> review via scripts/atc_cli.py pipeline' \
		'  make paper-claim   - run a one-shot paper claim session via scripts/atc_cli.py paper-claim' \
		'  make theorem-dedupe - delete later theorems whose theorem types are definitionally equivalent' \
		'  make rewrite       - run scripts/atc_cli.py rewrite' \
		'  make review        - run scripts/atc_cli.py review' \
		'  make materialize-generated - split MATERIALIZE_DERIVED_FILE into Generated chunks and rebuild manifest/catalog' \
		'  make materialize-reviewed-generated - materialize REVIEWED_FILE without first copying it onto Derived.lean' \
		'  make refactor-to-generated - run theorem-dedupe -> pass1.5 -> pass2 -> materialize generated' \
		'  make research-agenda REPORT_FILE=materials/your_report.md - regenerate AutomatedTheoryConstruction/research_agenda.md' \
		'  make materials-cache - build materials-derived files and refresh data/materials_cache' \
		'  make materials-derive - build materials-derived files only, without fetch/extract' \
		'  make data-migrate-layout-dry-run - show how legacy data/* files would move into role directories' \
		'  make data-migrate-layout - migrate legacy data/* files into role directories' \
		'' \
		'Common overrides:' \
		'  WORKER_COMMAND="uv run scripts/mock_worker.py"' \
		'  WORKER_TIMEOUT=600 CODEX_TIMEOUT=540' \
		'  ATC_COMMON_ARGS="--config configs/atc.continue.json"' \
		'  THEORY_FILE=... DERIVED_FILE=... SCRATCH_FILE=...' \
		'  MATERIALIZE_DERIVED_FILE=...  # override materialize-generated input explicitly' \
		'  CONTINUE_CONFIG=configs/atc.continue.json' \
		'  ALPHA_DEDUPE_EQUIVALENCE_MODE=defeq|alpha' \
		'  THEORY_FILE should point to the Theory.lean entry module' \
		'  SEED_ARGS="--context-file path/to/context.tex --seed-count 4"' \
		'  LOOP_ARGS="--max-iterations 40"' \
		'  CYCLE_ARGS="--cycle-iterations 20 --snapshot-root snapshots"' \
		'  PAPER_CLAIM_ARGS="--skip-verify --current-iteration 0"' \
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

test:
	@for f in tests/*_test.py; do \
		printf '[test] %s\n' "$$f"; \
		python3 "$$f" || exit 1; \
	done

data-migrate-layout-dry-run:
	python3 scripts/migrate_data_layout.py

data-migrate-layout:
	python3 scripts/migrate_data_layout.py --apply

seed:
	$(ATC) seed \
		$(ATC_COMMON_ARGS) \
		--theory-file $(THEORY_FILE) \
		--derived-file $(DERIVED_FILE) \
		--seeds-file $(SEEDS_FILE) \
		$(SEED_ARGS)

seed-loop-refactor-to-generated: seed loop-refactor-to-generated

materials-cache:
	$(PYTHON) scripts/materials_sync.py --materials-dir materials

materials-derive:
	$(PYTHON) scripts/materials_sync.py --materials-dir materials --derive-only

research-agenda:
	@test -n "$(REPORT_FILE)" || { echo 'REPORT_FILE is required, e.g. make research-agenda REPORT_FILE=materials/your_report.md'; exit 1; }
	$(ATC) research-agenda --report-file $(REPORT_FILE)

loop:
	$(ATC) loop \
		$(ATC_COMMON_ARGS) \
		--worker-command "$(WORKER_COMMAND)" \
		--worker-timeout "$(WORKER_TIMEOUT)" \
		--codex-timeout "$(CODEX_TIMEOUT)" \
		$(LOOP_ARGS)

loop-continue:
	$(ATC) loop \
		$(ATC_COMMON_ARGS) \
		--worker-command "$(WORKER_COMMAND)" \
		--worker-timeout "$(WORKER_TIMEOUT)" \
		--codex-timeout "$(CODEX_TIMEOUT)" \
		--no-initialize-on-start \
		$(LOOP_ARGS)

loop-refactor-to-generated: loop refactor-to-generated

loop-continue-refactor-to-generated: ATC_COMMON_ARGS = --config $(CONTINUE_CONFIG)
loop-continue-refactor-to-generated: loop-continue refactor-to-generated

cycle:
	$(ATC) cycle \
		$(ATC_COMMON_ARGS) \
		--worker-command "$(WORKER_COMMAND)" \
		--worker-timeout "$(WORKER_TIMEOUT)" \
		--codex-timeout "$(CODEX_TIMEOUT)" \
		--snapshot-root $(SNAPSHOT_ROOT) \
		$(CYCLE_ARGS)

pipeline:
	$(ATC) pipeline \
		$(ATC_COMMON_ARGS) \
		--worker-command "$(WORKER_COMMAND)" \
		--worker-timeout "$(WORKER_TIMEOUT)" \
		--codex-timeout "$(CODEX_TIMEOUT)" \
		--preview-file $(PREVIEW_FILE) \
		--review-output-file $(REVIEWED_FILE) \
		$(PIPELINE_ARGS)

paper-claim:
	$(ATC) paper-claim \
		$(ATC_COMMON_ARGS) \
		--theory-file $(THEORY_FILE) \
		--derived-file $(DERIVED_FILE) \
		--scratch-file $(SCRATCH_FILE) \
		$(PAPER_CLAIM_ARGS)

theorem-dedupe alpha-dedupe:
	cp $(DERIVED_FILE) $(PREVIEW_FILE)
	$(PYTHON) scripts/refactor/delete_alpha_equiv_duplicates.py \
		--input-file $(PREVIEW_FILE) \
		--output-file $(PREVIEW_FILE) \
		--alpha-source-file $(DERIVED_FILE) \
		--build-target AutomatedTheoryConstruction.Derived \
		--equivalence-mode $(ALPHA_DEDUPE_EQUIVALENCE_MODE) \
		--report-file $(ALPHA_DEDUPE_REPORT_FILE)

rewrite:
	$(ATC) rewrite \
		$(ATC_COMMON_ARGS) \
		--input-file $(PREVIEW_FILE) \
		--output-file $(PREVIEW_FILE) \
		--raw-output-file $(TRY_AT_EACH_STEP_RAW_OUTPUT_FILE) \
		--apply-report-file $(TRY_AT_EACH_STEP_APPLY_REPORT_FILE) \
		$(REWRITE_ARGS)

review:
	$(ATC) review \
		$(ATC_COMMON_ARGS) \
		--input-file $(PREVIEW_FILE) \
		--output-file $(REVIEWED_FILE) \
		$(REVIEW_ARGS)

materialize-generated:
	$(ATC) materialize-generated \
		$(ATC_COMMON_ARGS) \
		--derived-file $(MATERIALIZE_DERIVED_FILE) \
		--deps-file $(DEPS_FILE) \
		--generated-root $(GENERATED_ROOT) \
		--manifest-file $(GENERATED_MANIFEST_FILE) \
		--catalog-file $(GENERATED_CATALOG_FILE) \
		--plan-file $(DERIVED_CHUNK_PLAN_FILE) \
		$(MATERIALIZE_ARGS)

materialize-reviewed-generated: MATERIALIZE_DERIVED_FILE=$(REVIEWED_FILE)
materialize-reviewed-generated: MATERIALIZE_ARGS+=--no-reset-derived
materialize-reviewed-generated: materialize-generated

refactor-to-generated:
	cp $(DERIVED_FILE) $(PREVIEW_FILE)
	$(PYTHON) scripts/refactor/delete_alpha_equiv_duplicates.py \
		--input-file $(PREVIEW_FILE) \
		--output-file $(PREVIEW_FILE) \
		--alpha-source-file $(DERIVED_FILE) \
		--build-target AutomatedTheoryConstruction.Derived \
		--equivalence-mode $(ALPHA_DEDUPE_EQUIVALENCE_MODE) \
		--report-file $(ALPHA_DEDUPE_REPORT_FILE)
	$(ATC) rewrite \
		$(ATC_COMMON_ARGS) \
		--input-file $(PREVIEW_FILE) \
		--output-file $(PREVIEW_FILE) \
		--raw-output-file $(TRY_AT_EACH_STEP_RAW_OUTPUT_FILE) \
		--apply-report-file $(TRY_AT_EACH_STEP_APPLY_REPORT_FILE) \
		$(REWRITE_ARGS)
	$(ATC) review \
		$(ATC_COMMON_ARGS) \
		--input-file $(PREVIEW_FILE) \
		--output-file $(REVIEWED_FILE) \
		$(REVIEW_ARGS)
	cp $(REVIEWED_FILE) $(DERIVED_FILE)
	$(ATC) materialize-generated \
		$(ATC_COMMON_ARGS) \
		--derived-file $(DERIVED_FILE) \
		--deps-file $(DEPS_FILE) \
		--generated-root $(GENERATED_ROOT) \
		--manifest-file $(GENERATED_MANIFEST_FILE) \
		--catalog-file $(GENERATED_CATALOG_FILE) \
		--plan-file $(DERIVED_CHUNK_PLAN_FILE) \
		$(MATERIALIZE_ARGS)
