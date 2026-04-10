from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    with tempfile.TemporaryDirectory() as tmp_dir:
        root = Path(tmp_dir)
        input_file = root / "input.lean"
        input_file.write_text("theorem foo : True := by trivial\n", encoding="utf-8")

        completed = subprocess.run(
            [
                sys.executable,
                str(REPO_ROOT / "scripts" / "apply_try_at_each_step_rewrites.py"),
                "--input-file",
                str(input_file),
                "--dry-run",
            ],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            check=False,
        )
        if completed.returncode != 0:
            raise RuntimeError(f"rewrite dry-run failed: stdout={completed.stdout!r} stderr={completed.stderr!r}")
        payload = json.loads(completed.stdout)
        if payload["status"] != "noop":
            raise RuntimeError(f"unexpected rewrite report: {payload}")
        if "raw_output_file" in payload or "apply_report_file" in payload:
            raise RuntimeError(f"rewrite dry-run should not mention output files by default: {payload}")

        cli_completed = subprocess.run(
            [
                sys.executable,
                str(REPO_ROOT / "scripts" / "atc_cli.py"),
                "rewrite",
                "--input-file",
                str(input_file),
                "--dry-run",
            ],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            check=False,
        )
        if cli_completed.returncode != 0:
            raise RuntimeError(
                f"atc rewrite dry-run failed: stdout={cli_completed.stdout!r} stderr={cli_completed.stderr!r}"
            )
        if "--raw-output-file" in cli_completed.stderr or "--apply-report-file" in cli_completed.stderr:
            raise RuntimeError(f"CLI should not pass tryAtEachStep artifact paths by default: {cli_completed.stderr!r}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
