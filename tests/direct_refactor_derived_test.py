from __future__ import annotations

import contextlib
import io
import json
import subprocess
import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))


import direct_refactor_derived as review_mod


def _run_main(argv: list[str]) -> tuple[int, str, str]:
    stdout_buffer = io.StringIO()
    stderr_buffer = io.StringIO()
    old_argv = sys.argv
    try:
        sys.argv = argv
        with contextlib.redirect_stdout(stdout_buffer), contextlib.redirect_stderr(stderr_buffer):
            code = review_mod.main()
    finally:
        sys.argv = old_argv
    return code, stdout_buffer.getvalue(), stderr_buffer.getvalue()


def main() -> int:
    original_run_llm_exec = review_mod.run_llm_exec
    try:
        with tempfile.TemporaryDirectory() as tmp_dir:
            root = Path(tmp_dir)
            input_file = root / "input.lean"
            output_file = root / "output.lean"
            report_file = root / "report.json"
            policy_file = root / "policy.md"
            lean_rule_file = root / "lean-rule.md"
            mathlib_usage_file = root / "mathlib-usage.md"
            input_file.write_text("theorem foo : True := by trivial\n", encoding="utf-8")
            for path in (policy_file, lean_rule_file, mathlib_usage_file):
                path.write_text("placeholder\n", encoding="utf-8")

            def fake_run_llm_exec(**_: object) -> subprocess.CompletedProcess[str]:
                return subprocess.CompletedProcess(
                    args=["codex"],
                    returncode=0,
                    stdout="worker stdout line 1\nworker stdout line 2\n",
                    stderr="worker stderr line 1\n",
                )

            review_mod.run_llm_exec = fake_run_llm_exec
            code, stdout_text, stderr_text = _run_main(
                [
                    "direct_refactor_derived.py",
                    "--input-file",
                    str(input_file),
                    "--output-file",
                    str(output_file),
                    "--report-file",
                    str(report_file),
                    "--policy-file",
                    str(policy_file),
                    "--lean-rule-file",
                    str(lean_rule_file),
                    "--mathlib-usage-file",
                    str(mathlib_usage_file),
                ]
            )
            if code != 0:
                raise RuntimeError(f"expected success, got {code}: stdout={stdout_text!r} stderr={stderr_text!r}")
            report = json.loads(stdout_text)
            if report["status"] != "ok":
                raise RuntimeError(f"unexpected report: {report}")
            if "stdout_excerpt" in report or "stderr_excerpt" in report:
                raise RuntimeError(f"success report should not include raw worker excerpts: {report}")
            if "worker stdout line 1" in stdout_text or "worker stderr line 1" in stderr_text:
                raise RuntimeError("worker output should be suppressed by default")

            code, stdout_text, stderr_text = _run_main(
                [
                    "direct_refactor_derived.py",
                    "--input-file",
                    str(input_file),
                    "--output-file",
                    str(output_file),
                    "--report-file",
                    str(report_file),
                    "--policy-file",
                    str(policy_file),
                    "--lean-rule-file",
                    str(lean_rule_file),
                    "--mathlib-usage-file",
                    str(mathlib_usage_file),
                    "--print-worker-output",
                ]
            )
            if code != 0:
                raise RuntimeError(f"expected success with raw output, got {code}")
            if "worker stdout line 1" not in stdout_text:
                raise RuntimeError(f"expected worker stdout in raw-output mode: {stdout_text!r}")
            if "worker stderr line 1" not in stderr_text:
                raise RuntimeError(f"expected worker stderr in raw-output mode: {stderr_text!r}")
    finally:
        review_mod.run_llm_exec = original_run_llm_exec
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
