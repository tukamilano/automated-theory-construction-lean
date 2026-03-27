SHELL := /bin/sh

LAKE ?= lake
PYTHON ?= uv run python

THEORY_FILE ?= AutomatedTheoryConstruction/Theory.lean
DERIVED_FILE ?= AutomatedTheoryConstruction/Derived.lean
SCRATCH_FILE ?= AutomatedTheoryConstruction/Scratch.lean
SEEDS_FILE ?= AutomatedTheoryConstruction/seeds.jsonl
PREVIEW_FILE ?= AutomatedTheoryConstruction/Derived.refactored.preview.lean
REVIEWED_FILE ?= AutomatedTheoryConstruction/Derived.refactored.reviewed.lean

WORKER_COMMAND ?= uv run python scripts/codex_worker.py
WORKER_TIMEOUT ?= 420
CODEX_TIMEOUT ?= 390

SEED_ARGS ?=
LOOP_ARGS ?=
PIPELINE_ARGS ?=
REFACTOR_ARGS ?=
REVIEW_ARGS ?=

.PHONY: help build check check-theory check-derived check-scratch seed loop pipeline refactor review

help:
	@printf '%s\n' \
		'Available targets:' \
		'  make build         - lake build' \
		'  make check         - check Theory, Derived, Scratch' \
		'  make check-theory  - lake env lean $(THEORY_FILE)' \
		'  make check-derived - lake env lean $(DERIVED_FILE)' \
		'  make check-scratch - lake env lean $(SCRATCH_FILE)' \
		'  make seed          - generate seeds.jsonl (extra flags via SEED_ARGS=...)' \
		'  make loop          - run scripts/run_loop.py with worker defaults' \
		'  make pipeline      - run scripts/run_pipeline.py with worker defaults' \
		'  make refactor      - run scripts/refactor_derived.py' \
		'  make review        - run scripts/direct_refactor_derived.py' \
		'' \
		'Common overrides:' \
		'  WORKER_COMMAND="uv run python scripts/mock_worker.py"' \
		'  WORKER_TIMEOUT=600 CODEX_TIMEOUT=540' \
		'  THEORY_FILE=... DERIVED_FILE=... SCRATCH_FILE=...' \
		'  THEORY_FILE should point to the Theory.lean entry module' \
		'  SEED_ARGS="--context-file path/to/context.tex --seed-count 4"' \
		'  LOOP_ARGS="--no-initialize-on-start --max-iterations 40"' \
		'  PIPELINE_ARGS="--article-file path/to/context.tex --max-iterations 40"'

build:
	$(LAKE) build

check: check-theory check-derived check-scratch

check-theory:
	$(LAKE) env lean $(THEORY_FILE)

check-derived:
	$(LAKE) env lean $(DERIVED_FILE)

check-scratch:
	$(LAKE) env lean $(SCRATCH_FILE)

seed:
	$(PYTHON) scripts/generate_seeds_from_theory.py \
		--theory-file $(THEORY_FILE) \
		--derived-file $(DERIVED_FILE) \
		--output-file $(SEEDS_FILE) \
		$(SEED_ARGS)

loop:
	ATC_WORKER_COMMAND="$(WORKER_COMMAND)" \
	ATC_WORKER_TIMEOUT="$(WORKER_TIMEOUT)" \
	ATC_CODEX_TIMEOUT="$(CODEX_TIMEOUT)" \
	$(PYTHON) scripts/run_loop.py --enable-worker $(LOOP_ARGS)

pipeline:
	ATC_CODEX_TIMEOUT="$(CODEX_TIMEOUT)" \
	$(PYTHON) scripts/run_pipeline.py \
		--worker-command "$(WORKER_COMMAND)" \
		--worker-timeout "$(WORKER_TIMEOUT)" \
		$(PIPELINE_ARGS)

refactor:
	$(PYTHON) scripts/refactor_derived.py \
		--derived-file $(DERIVED_FILE) \
		--theory-file $(THEORY_FILE) \
		--output-file $(PREVIEW_FILE) \
		--worker-command "$(WORKER_COMMAND)" \
		--worker-timeout "$(WORKER_TIMEOUT)" \
		$(REFACTOR_ARGS)

review:
	$(PYTHON) scripts/direct_refactor_derived.py \
		--input-file $(PREVIEW_FILE) \
		--output-file $(REVIEWED_FILE) \
		$(REVIEW_ARGS)
