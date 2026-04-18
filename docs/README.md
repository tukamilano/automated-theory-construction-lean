# Documentation Guide

This directory is split by user task rather than by subsystem.
If you are unsure where to start, use the table below.

| Goal | Read |
| --- | --- |
| First setup and first successful run | [`GETTING_STARTED.md`](GETTING_STARTED.md) |
| Normal day-to-day operation | [`USER_GUIDE.md`](USER_GUIDE.md) |
| What files are user-owned vs runtime-managed | [`REPO_MAP.md`](REPO_MAP.md) |
| Replace the Lean verification backend | [`PROOF_EXECUTOR.md`](PROOF_EXECUTOR.md) |
| Runtime internals and implementation notes | [`../design/RUNTIME.md`](../design/RUNTIME.md) |

## Recommended Reading Order

### New to the repository

1. [`../README.md`](../README.md)
2. [`GETTING_STARTED.md`](GETTING_STARTED.md)
3. [`REPO_MAP.md`](REPO_MAP.md)
4. [`USER_GUIDE.md`](USER_GUIDE.md)

### Running the loop regularly

1. [`USER_GUIDE.md`](USER_GUIDE.md)
2. [`REPO_MAP.md`](REPO_MAP.md)

### Customizing advanced verification behavior

1. [`USER_GUIDE.md`](USER_GUIDE.md)
2. [`PROOF_EXECUTOR.md`](PROOF_EXECUTOR.md)
3. [`../design/RUNTIME.md`](../design/RUNTIME.md)

## Document Boundaries

- `README.md`: project overview, value proposition, and the shortest path to a first run
- `GETTING_STARTED.md`: prerequisites, setup, first files to edit, first commands to run
- `USER_GUIDE.md`: operational workflows and common commands after setup
- `REPO_MAP.md`: ownership boundaries and which files are normally edited by hand
- `PROOF_EXECUTOR.md`: external verifier contract only
