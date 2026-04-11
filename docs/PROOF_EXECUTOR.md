# Proof Engine Interface

This repository treats Lean final verification as a separate `Proof Engine` while planning, theorem generation, and repair remain in the existing worker loop.
That means you can replace only the `Proof Engine` and connect another system without changing the higher-level solver pipeline.

## Overview

Verification is executed by `verify_scratch()` in `scripts/lean_verify.py`.

- Default behavior: run `lake env lean <Scratch.lean>` directly and evaluate success/failure.
- Replacement behavior: when `ATC_PROOF_EXECUTOR` is set, invoke an external command and exchange JSON over stdin/stdout.
- When `ATC_PROOF_EXECUTOR` is set, output is treated as **JSON-only** by default (no mixed logging on stdout).
- If your external implementation prints mixed output, set `ATC_PROOF_EXECUTOR_LENIENT_JSON=1` to accept a tolerant mode.

```bash
export ATC_PROOF_EXECUTOR="uv run python path/to/my_proof_executor.py"
uv run python scripts/atc_cli.py loop ...
```

## Executor Contract

### Input (external command stdin)

```json
{
  "problem_id": "string",
  "mode": "proof | counterexample",
  "scratch_file": "/absolute/path/to/AutomatedTheoryConstruction/Scratch.lean",
  "timeout_sec": 60
}
```

### Output (stdout)

The minimum required keys for pass/fail evaluation are:

```json
{
  "problem_id": "string",
  "mode": "proof | counterexample",
  "success": true,
  "duration_ms": 1234,
  "stdout": "",
  "stderr": "",
  "error_category": "executor_failure_category",
  "diagnostics": ["line1", "line2"],
  "executor_metadata": {
    "executor_type": "external",
    "executor_command": "...",
    "toolchain": "...",
    "scratch_sha256": "...",
    "scratch_file": "...",
    "timeout_sec": 60,
    "mode": "proof | counterexample"
  }
}
```

`error_category` can be a string or array. `diagnostics` can also be a string or array and is preferred by `run_loop` repair logic when present.
When `success` is `false`, include substantial debug text in `stderr/stdout` to improve repair quality.
`executor_metadata` is recommended for reproducibility; including `toolchain` and `scratch_sha256` helps trace differences even when the same problem is retried.

### Failure handling

- Non-zero exit code: interpreted as `success: false`.
- JSON parse failure: treat it as `success: false` with diagnostics in `stderr`.
- Timeout: recommended to also enforce the same timeout (`timeout_sec`) in the external process.
- `ATC_PROOF_EXECUTOR_LENIENT_JSON=1` is a transitional compatibility mode for external implementations that print mixed stdout; long-term, stdout should be JSON-only.

## Minimal implementation example

```python
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path

def main() -> None:
    request = json.load(sys.stdin)
    scratch_file = Path(request["scratch_file"])
    timeout_sec = request.get("timeout_sec")
    started_at = time.monotonic()

    # Run your custom proof engine here.
    proc = subprocess.run(
        ["lake", "env", "lean", str(scratch_file)],
        capture_output=True,
        text=True,
        timeout=timeout_sec,
    )

    scratch_content = scratch_file.read_bytes()
    scratch_sha256 = hashlib.sha256(scratch_content).hexdigest()

    out = {
        "problem_id": request["problem_id"],
        "mode": request["mode"],
        "success": proc.returncode == 0,
        "duration_ms": int((time.monotonic() - started_at) * 1000),
        "error_category": "local_lean_result" if proc.returncode != 0 else "local_lean_ok",
        "diagnostics": proc.stderr,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
        "executor_metadata": {
            "executor_type": "external",
            "executor_command": " ".join(sys.argv),
            "scratch_file": str(scratch_file),
            "timeout_sec": timeout_sec,
            "toolchain": "local",
            "scratch_sha256": scratch_sha256,
            "mode": request["mode"],
        },
    }
    print(json.dumps(out))


if __name__ == "__main__":
    main()
```

## Replacement steps (tutorial)

1. Create an external verifier executable.
   - Implement it as a CLI invoked by `ATC_PROOF_EXECUTOR`.
   - Read the input JSON, run verification, and write result JSON to stdout.
   - Echo back `problem_id` and `mode` unchanged.

2. Return fields compatible with the loop: `success/stdout/stderr/duration_ms`.
   - Put failure details in `stderr`.
   - Return `success` strictly as a boolean.

3. Run in production by setting environment variables

   ```bash
   export ATC_PROOF_EXECUTOR="uv run python my_proof_executor.py"
   uv run python scripts/atc_cli.py loop --max-iterations 20
   ```

4. On poor convergence, inspect logs and align the contract.
   - Keep worker logic and prompts unchanged; only adjust verifier output.
   - Increase signal density in `stdout/stderr` to improve reproducibility.

## Operational notes

- If you unset `ATC_PROOF_EXECUTOR`, execution automatically returns to default `lake env lean` verification.
- For local/remote split deployments, enforcing `timeout_sec` in the external runtime is safer.
- The existing repair loop only needs success/failure plus diagnostics, so your proof generator can remain unchanged.
