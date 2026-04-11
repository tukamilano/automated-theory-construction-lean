from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))

import lean_verify


def _mock_executor_source() -> str:
    return """from __future__ import annotations

import json
import os
import sys


request = json.loads(sys.stdin.read())
problem_id = str(request.get("problem_id", ""))
mode = str(request.get("mode", ""))
scenario = os.environ.get("ATC_MOCK_PROOF_EXECUTOR_SCENARIO", "success")

if scenario == "success":
    response = {
        "problem_id": problem_id,
        "mode": mode,
        "success": True,
        "duration_ms": 17,
        "stdout": "ok",
        "stderr": "",
    }
    print(json.dumps(response))
elif scenario == "contract_mismatch":
    response = {
        "problem_id": "different-problem-id",
        "mode": "counterexample",
        "success": True,
        "duration_ms": 12,
        "stdout": "",
        "stderr": "",
    }
    print(json.dumps(response))
elif scenario == "strict_parse_error":
    print("executor log: failed internally")
    print(json.dumps({"problem_id": problem_id, "mode": mode, "success": True}))
elif scenario == "lenient_parse":
    print("executor note")
    print(json.dumps({"problem_id": problem_id, "mode": mode, "success": True, "duration_ms": 21, "stdout": "ok"}))
elif scenario == "nonzero_exit":
    print(json.dumps({"problem_id": problem_id, "mode": mode, "success": False}))
    sys.exit(2)
else:
    response = {"problem_id": problem_id, "mode": mode, "success": False}
    print(json.dumps(response))
"""


def _write_mock_executor(executor_path: Path) -> None:
    executor_path.parent.mkdir(parents=True, exist_ok=True)
    executor_path.write_text(_mock_executor_source(), encoding="utf-8")


def _run_with_mock_executor(scenario: str, *, lenient_json: bool | None = None) -> dict:
    with tempfile.TemporaryDirectory() as tmpdir:
        root = Path(tmpdir)
        scratch_file = root / "AutomatedTheoryConstruction" / "Scratch.lean"
        scratch_file.parent.mkdir(parents=True, exist_ok=True)
        scratch_file.write_text("theorem test : True := by decide\n", encoding="utf-8")

        executor_path = root / "mock_proof_executor.py"
        _write_mock_executor(executor_path)
        command = f"{sys.executable} {executor_path}"

        old_atc = os.environ.get("ATC_PROOF_EXECUTOR")
        old_mock = os.environ.get("ATC_MOCK_PROOF_EXECUTOR_SCENARIO")
        old_lenient = os.environ.get("ATC_PROOF_EXECUTOR_LENIENT_JSON")
        try:
            os.environ.update(
                {
                    "ATC_PROOF_EXECUTOR": command,
                    "ATC_MOCK_PROOF_EXECUTOR_SCENARIO": scenario,
                }
            )
            if lenient_json is None:
                os.environ.pop("ATC_PROOF_EXECUTOR_LENIENT_JSON", None)
            else:
                os.environ["ATC_PROOF_EXECUTOR_LENIENT_JSON"] = "1" if lenient_json else "0"

            return lean_verify.verify_scratch(
                problem_id="op_000001",
                mode="proof",
                scratch_file=scratch_file,
                timeout_sec=2,
            )
        finally:
            if old_atc is None:
                os.environ.pop("ATC_PROOF_EXECUTOR", None)
            else:
                os.environ["ATC_PROOF_EXECUTOR"] = old_atc

            if old_mock is None:
                os.environ.pop("ATC_MOCK_PROOF_EXECUTOR_SCENARIO", None)
            else:
                os.environ["ATC_MOCK_PROOF_EXECUTOR_SCENARIO"] = old_mock

            if old_lenient is None:
                os.environ.pop("ATC_PROOF_EXECUTOR_LENIENT_JSON", None)
            else:
                os.environ["ATC_PROOF_EXECUTOR_LENIENT_JSON"] = old_lenient


def test_external_executor_success() -> None:
    result = _run_with_mock_executor("success")
    if not result.get("success"):
        raise RuntimeError(f"expected executor success, got: {result}")
    if result.get("problem_id") != "op_000001" or result.get("mode") != "proof":
        raise RuntimeError(f"unexpected metadata in success result: {result}")

    metadata = result.get("executor_metadata")
    if not isinstance(metadata, dict) or metadata.get("executor_type") != "external":
        raise RuntimeError(f"expected external executor metadata, got: {metadata}")

    command = result.get("command")
    if not isinstance(command, list) or len(command) != 2:
        raise RuntimeError(f"unexpected command shape: {command!r}")


def test_external_executor_nonzero_exit() -> None:
    result = _run_with_mock_executor("nonzero_exit")
    if result.get("success"):
        raise RuntimeError(f"expected executor failure, got: {result}")
    if result.get("error_category") != "executor_exit_error":
        raise RuntimeError(f"expected executor_exit_error, got: {result}")


def test_external_executor_contract_violation() -> None:
    result = _run_with_mock_executor("contract_mismatch")
    if result.get("success"):
        raise RuntimeError(f"expected contract violation to fail verification, got: {result}")
    if result.get("error_category") != "executor_contract_violation":
        raise RuntimeError(f"expected executor_contract_violation, got: {result}")
    if "problem_id mismatch" not in str(result.get("stderr", "")):
        raise RuntimeError(f"expected mismatch detail in stderr, got: {result.get('stderr')!r}")


def test_external_executor_strict_json_rejects_noisy_output() -> None:
    result = _run_with_mock_executor("strict_parse_error")
    if result.get("success"):
        raise RuntimeError(f"expected parse error, got: {result}")
    if result.get("error_category") != "executor_output_parse_error":
        raise RuntimeError(f"expected executor_output_parse_error, got: {result}")


def test_external_executor_lenient_parses_embedded_json() -> None:
    result = _run_with_mock_executor("lenient_parse", lenient_json=True)
    if not result.get("success"):
        raise RuntimeError(f"expected lenient parse success, got: {result}")
    if result.get("error_category") is not None:
        raise RuntimeError(f"did not expect any error_category, got: {result.get('error_category')!r}")


def main() -> int:
    test_external_executor_success()
    test_external_executor_nonzero_exit()
    test_external_executor_contract_violation()
    test_external_executor_strict_json_rejects_noisy_output()
    test_external_executor_lenient_parses_embedded_json()
    print("proof executor tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
