from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shlex
import subprocess
import time
from pathlib import Path
from typing import Any


def _env_truthy(name: str, default: bool = False) -> bool:
    value = (os.getenv(name) or "").strip().lower()
    if not value:
        return default
    return value in {"1", "true", "yes", "on"}


def _coerce_int(value: Any, default: int) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def _coerce_bool(value: Any) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, int):
        return bool(value)
    if isinstance(value, str):
        return value.strip().lower() in {"1", "true", "yes", "on"}
    return False


def _normalize_lines(value: Any) -> list[str]:
    if value is None:
        return []
    if isinstance(value, list):
        return [str(item).strip() for item in value if str(item).strip()]
    if isinstance(value, str):
        return [line.strip() for line in value.splitlines() if line.strip()]
    return [str(value).strip()] if str(value).strip() else []


def _file_sha256(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def _read_toolchain() -> str:
    toolchain_path = Path(__file__).resolve().parent.parent / "lean-toolchain"
    if not toolchain_path.exists():
        return ""
    try:
        for line in toolchain_path.read_text(encoding="utf-8").splitlines():
            text = line.strip()
            if text:
                return text
    except OSError:
        return ""
    return ""


def _build_executor_metadata(command: list[str], mode: str, scratch_file: Path, timeout_sec: int | None) -> dict[str, Any]:
    return {
        "executor_type": "external",
        "executor_command": " ".join(command),
        "mode": mode,
        "scratch_file": str(scratch_file),
        "timeout_sec": timeout_sec,
        "toolchain": _read_toolchain(),
        "scratch_sha256": _file_sha256(scratch_file),
    }


def _build_local_metadata(mode: str, scratch_file: Path, timeout_sec: int | None) -> dict[str, Any]:
    return {
        "executor_type": "local",
        "command": "lake env lean",
        "mode": mode,
        "scratch_file": str(scratch_file),
        "timeout_sec": timeout_sec,
        "toolchain": _read_toolchain(),
        "scratch_sha256": _file_sha256(scratch_file),
    }


def _find_fenced_json_blocks(raw: str) -> list[str]:
    return re.findall(r"```json\s*(\{.*?\})\s*```", raw, flags=re.DOTALL | re.IGNORECASE)


def _is_valid_executor_payload(payload: Any) -> bool:
    if not isinstance(payload, dict):
        return False
    return all(key in payload for key in ("problem_id", "mode", "success"))


def _extract_json_object(text: str, *, strict: bool) -> dict[str, Any]:
    raw = text.strip()
    if not raw:
        raise ValueError("executor returned empty output")

    parse_candidates: list[str] = [raw]
    if not strict:
        start_idx: int | None = None
        depth = 0
        in_string = False
        escape = False
        for idx, ch in enumerate(raw):
            if in_string:
                if escape:
                    escape = False
                elif ch == "\\":
                    escape = True
                elif ch == '"':
                    in_string = False
                continue
            if ch == '"':
                in_string = True
                continue
            if ch == "{":
                if depth == 0:
                    start_idx = idx
                depth += 1
                continue
            if ch == "}" and depth > 0:
                depth -= 1
                if depth == 0 and start_idx is not None:
                    parse_candidates.append(raw[start_idx : idx + 1])
                    start_idx = None
        parse_candidates.extend(_find_fenced_json_blocks(raw))

    parse_errors: list[str] = []
    for candidate in parse_candidates:
        try:
            payload = json.loads(candidate)
        except json.JSONDecodeError as exc:
            parse_errors.append(str(exc))
            continue
        if _is_valid_executor_payload(payload):
            return payload
        parse_errors.append(
            "missing required executor fields: problem_id, mode, success"
        )

    message = "; ".join(parse_errors) if parse_errors else "not a JSON object"
    if strict:
        raise ValueError(
            f"executor output must be a single JSON object; got parse error: {message}"
        )
    raise ValueError(f"executor output is not a JSON object ({message})")


def _run_external_proof_executor(
    problem_id: str,
    mode: str,
    scratch_file: Path,
    timeout_sec: int | None,
) -> dict[str, Any]:
    executor_command = os.getenv("ATC_PROOF_EXECUTOR", "").strip()
    if not executor_command:
        raise RuntimeError("proof executor command is empty")

    cmd = shlex.split(executor_command)
    if not cmd:
        raise RuntimeError("ATC_PROOF_EXECUTOR is not parseable as a command")

    strict_json = not _env_truthy("ATC_PROOF_EXECUTOR_LENIENT_JSON")
    request_payload = {
        "problem_id": problem_id,
        "mode": mode,
        "scratch_file": str(scratch_file),
        "timeout_sec": timeout_sec,
    }
    metadata = _build_executor_metadata(cmd, mode, scratch_file, timeout_sec)
    started = time.monotonic()
    try:
        completed = subprocess.run(
            cmd,
            input=json.dumps(request_payload, ensure_ascii=False),
            text=True,
            capture_output=True,
            timeout=timeout_sec,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        duration_ms = int((time.monotonic() - started) * 1000)
        timeout_label = f"{timeout_sec}s" if timeout_sec is not None else "without a time limit"
        return {
            "problem_id": problem_id,
            "mode": mode,
            "success": False,
            "command": cmd,
            "duration_ms": duration_ms,
            "stderr": f"Proof executor timed out after {timeout_label}\n{exc.stderr or ''}".strip(),
            "stdout": str(exc.stdout or ""),
            "error_category": "executor_timeout",
            "diagnostics": f"Proof executor timed out after {timeout_label}",
            "executor_metadata": metadata,
        }

    duration_ms = int((time.monotonic() - started) * 1000)
    if completed.returncode != 0:
        return {
            "problem_id": problem_id,
            "mode": mode,
            "success": False,
            "command": cmd,
            "duration_ms": duration_ms,
            "stderr": (completed.stderr or "").strip(),
            "stdout": (completed.stdout or "").strip(),
            "error_category": "executor_exit_error",
            "diagnostics": _normalize_lines(completed.stderr) + _normalize_lines(completed.stdout),
            "executor_metadata": metadata,
        }

    try:
        payload = _extract_json_object(completed.stdout, strict=strict_json)
    except ValueError as exc:
        return {
            "problem_id": problem_id,
            "mode": mode,
            "success": False,
            "command": cmd,
            "duration_ms": duration_ms,
            "stderr": f"Proof executor output parse error: {exc}",
            "stdout": (completed.stdout or "").strip(),
            "error_category": "executor_output_parse_error",
            "diagnostics": (completed.stdout or "").strip(),
            "executor_metadata": metadata,
        }

    actual_problem_id = str(payload.get("problem_id", "")).strip()
    actual_mode = str(payload.get("mode", "")).strip()
    if actual_problem_id != problem_id or actual_mode != mode:
        mismatch_details = []
        if actual_problem_id != problem_id:
            mismatch_details.append(f"problem_id mismatch: expected={problem_id!r}, actual={actual_problem_id!r}")
        if actual_mode != mode:
            mismatch_details.append(f"mode mismatch: expected={mode!r}, actual={actual_mode!r}")
        return {
            "problem_id": problem_id,
            "mode": mode,
            "success": False,
            "command": cmd,
            "duration_ms": duration_ms,
            "stderr": "; ".join(mismatch_details),
            "stdout": str(payload.get("stdout", "") or ""),
            "error_category": "executor_contract_violation",
            "diagnostics": _normalize_lines(payload.get("diagnostics", "")),
            "artifacts": payload.get("artifacts"),
            "executor_metadata": metadata,
        }

    success = _coerce_bool(payload.get("success"))
    result = {
        "problem_id": problem_id,
        "mode": mode,
        "success": bool(success),
        "command": payload.get("command", cmd),
        "duration_ms": _coerce_int(payload.get("duration_ms", duration_ms), duration_ms),
        "stderr": str(payload.get("stderr", "") or ""),
        "stdout": str(payload.get("stdout", "") or ""),
    }
    for key in ("error_category", "diagnostics", "artifacts", "error"):
        if key in payload:
            result[key] = payload[key]
    result.setdefault("executor_metadata", metadata)
    return result


def _run_local_lean(
    problem_id: str,
    mode: str,
    scratch_file: Path,
    timeout_sec: int | None,
) -> dict[str, Any]:
    cmd = ["lake", "env", "lean", str(scratch_file)]
    started = time.monotonic()
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout_sec)
    except subprocess.TimeoutExpired as exc:
        duration_ms = int((time.monotonic() - started) * 1000)
        stderr_text = (exc.stderr or "") if isinstance(exc.stderr, str) else ""
        stdout_text = (exc.stdout or "") if isinstance(exc.stdout, str) else ""
        timeout_label = f"{timeout_sec}s" if timeout_sec is not None else "without a time limit"
        return {
            "problem_id": problem_id,
            "success": False,
            "mode": mode,
            "command": cmd,
            "duration_ms": duration_ms,
            "stderr": f"Lean verification timed out after {timeout_label}\n{stderr_text}".strip(),
            "stdout": stdout_text,
            "error_category": "local_lean_timeout",
            "diagnostics": f"Lean verification timed out after {timeout_label}",
            "executor_metadata": _build_local_metadata(mode, scratch_file, timeout_sec),
        }
    duration_ms = int((time.monotonic() - started) * 1000)
    result = {
        "problem_id": problem_id,
        "success": proc.returncode == 0,
        "mode": mode,
        "command": cmd,
        "duration_ms": duration_ms,
        "stderr": proc.stderr or "",
        "stdout": proc.stdout or "",
        "executor_metadata": _build_local_metadata(mode, scratch_file, timeout_sec),
    }
    if not result["success"]:
        result["error_category"] = "local_lean_failure"
        result["diagnostics"] = _normalize_lines(proc.stderr) + _normalize_lines(proc.stdout)
    return result


def verify_scratch(problem_id: str, mode: str, scratch_file: Path, timeout_sec: int | None) -> dict[str, Any]:
    executor_command = os.getenv("ATC_PROOF_EXECUTOR", "").strip()
    if executor_command:
        return _run_external_proof_executor(
            problem_id=problem_id,
            mode=mode,
            scratch_file=scratch_file,
            timeout_sec=timeout_sec,
        )
    return _run_local_lean(problem_id=problem_id, mode=mode, scratch_file=scratch_file, timeout_sec=timeout_sec)


def main() -> None:
    parser = argparse.ArgumentParser(description="Verify Lean code in Scratch.lean")
    parser.add_argument("--problem-id", required=True)
    parser.add_argument("--mode", required=True, choices=["proof", "counterexample"])
    parser.add_argument("--scratch-file", default="AutomatedTheoryConstruction/Scratch.lean")
    parser.add_argument("--timeout", type=int, default=60)
    args = parser.parse_args()
    timeout_sec = None if args.timeout == 0 else args.timeout

    result = verify_scratch(
        problem_id=args.problem_id,
        mode=args.mode,
        scratch_file=Path(args.scratch_file),
        timeout_sec=timeout_sec,
    )
    print(json.dumps(result, ensure_ascii=False))


if __name__ == "__main__":
    main()
