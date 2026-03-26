ifneq (,$(wildcard .env))
include .env
export
endif

PYTHON ?= python3
UV ?= uv
MAX_ITERATIONS ?= 1
SEED_COUNT ?= 4
WORKER_TIMEOUT ?= 420
CODEX_TIMEOUT ?= 390
SEED_SANDBOX ?= read-only
WORKER_COMMAND ?= $(UV) run python scripts/codex_worker.py
CONTEXT_FILE ?=

.PHONY: help build verify-scratch mock-loop codex-loop continue-codex-loop seed-dry-run pipeline-dry-run

help: ## Show common entry points
	@awk 'BEGIN {FS = ": .*## "; print "Targets:"} /^[a-zA-Z0-9_.-]+: .*## / {printf "  %-20s %s\n", $$1, $$2}' $(MAKEFILE_LIST)

build: ## Build the Lean project
	lake build

verify-scratch: ## Type-check AutomatedTheoryConstruction/Scratch.lean
	lake env lean AutomatedTheoryConstruction/Scratch.lean

mock-loop: ## Run one local smoke iteration with the mock worker
	$(PYTHON) scripts/run_loop.py --enable-worker --worker-command "$(PYTHON) scripts/mock_worker.py" --max-iterations $(MAX_ITERATIONS) --no-phase-logs

codex-loop: ## Run the main loop with the Codex worker and default initialization
	ATC_CODEX_TIMEOUT=$(CODEX_TIMEOUT) $(PYTHON) scripts/run_loop.py --enable-worker --worker-command "$(WORKER_COMMAND)" --worker-timeout $(WORKER_TIMEOUT) --max-iterations $(MAX_ITERATIONS)

continue-codex-loop: ## Continue from current state without resetting Derived.lean and data/*
	ATC_CODEX_TIMEOUT=$(CODEX_TIMEOUT) $(PYTHON) scripts/run_loop.py --enable-worker --worker-command "$(WORKER_COMMAND)" --worker-timeout $(WORKER_TIMEOUT) --max-iterations $(MAX_ITERATIONS) --no-initialize-on-start

seed-dry-run: ## Print the seed-generation prompt and command without calling Codex
	$(PYTHON) scripts/generate_seeds_from_theory.py --dry-run --seed-count $(SEED_COUNT) $(if $(CONTEXT_FILE),--context-file $(CONTEXT_FILE),) --sandbox $(SEED_SANDBOX)

pipeline-dry-run: ## Print the full pipeline commands without executing them
	ATC_CODEX_TIMEOUT=$(CODEX_TIMEOUT) $(PYTHON) scripts/run_pipeline.py --dry-run --max-iterations $(MAX_ITERATIONS) --worker-command "$(WORKER_COMMAND)" --worker-timeout $(WORKER_TIMEOUT) $(if $(CONTEXT_FILE),--context-file $(CONTEXT_FILE),)
