from __future__ import annotations

import json
import os
import shlex
import subprocess
import re
from dataclasses import dataclass
from typing import Any


@dataclass(frozen=True)
class WorkerSettings:
    command: str
    timeout_sec: int


def load_worker_settings(
    command_override: str | None,
    timeout_override: int | None,
) -> WorkerSettings:
    command = (command_override or os.getenv("ATC_WORKER_COMMAND") or "").strip()
    timeout_text = (os.getenv("ATC_WORKER_TIMEOUT") or "").strip()
    timeout_from_env = int(timeout_text) if timeout_text else 180
    timeout_sec = timeout_override if timeout_override is not None else timeout_from_env

    if not command:
        raise ValueError("Worker command is required. Set --worker-command or ATC_WORKER_COMMAND.")
    if timeout_sec <= 0:
        raise ValueError("Worker timeout must be > 0 seconds.")

    return WorkerSettings(command=command, timeout_sec=timeout_sec)


def _iter_braced_json_candidates(text: str) -> list[str]:
    candidates: list[str] = []
    start_idx: int | None = None
    depth = 0
    in_string = False
    escape = False

    for idx, ch in enumerate(text):
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
                candidates.append(text[start_idx : idx + 1])
                start_idx = None

    return candidates


def _extract_json_object(text: str) -> tuple[dict[str, Any], int, bool]:
    raw = text.strip()
    if not raw:
        raise ValueError("Worker response is empty")

    parse_attempts = 0

    try:
        parse_attempts += 1
        payload = json.loads(raw)
        if isinstance(payload, dict):
            return payload, parse_attempts, False
    except json.JSONDecodeError:
        pass

    fenced_blocks = re.findall(r"```json\s*(\{.*?\})\s*```", raw, flags=re.DOTALL | re.IGNORECASE)
    for block in fenced_blocks:
        try:
            parse_attempts += 1
            payload = json.loads(block)
            if isinstance(payload, dict):
                return payload, parse_attempts, True
        except json.JSONDecodeError:
            continue

    for candidate in _iter_braced_json_candidates(raw):
        try:
            parse_attempts += 1
            payload = json.loads(candidate)
            if isinstance(payload, dict):
                return payload, parse_attempts, True
        except json.JSONDecodeError:
            continue

    raise ValueError("Worker response did not contain a parseable JSON object")


def invoke_worker_json(
    settings: WorkerSettings,
    task_type: str,
    system_prompt: str,
    payload: dict[str, Any],
    metadata: dict[str, Any] | None = None,
) -> tuple[dict[str, Any], dict[str, Any]]:
    request_body = {
        "task_type": task_type,
        "system_prompt": system_prompt,
        "payload": payload,
        "metadata": metadata or {},
    }

    cmd = shlex.split(settings.command)
    if not cmd:
        raise ValueError("Worker command could not be parsed")

    try:
        completed = subprocess.run(
            cmd,
            input=json.dumps(request_body, ensure_ascii=False),
            capture_output=True,
            text=True,
            timeout=settings.timeout_sec,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError(
            f"Worker timed out after {settings.timeout_sec}s. "
            "Try increasing --worker-timeout (or ATC_WORKER_TIMEOUT), e.g. 180-300."
        ) from exc

    if completed.returncode != 0:
        stderr = (completed.stderr or "").strip()
        raise RuntimeError(f"Worker exited with code {completed.returncode}: {stderr}")

    response, parse_attempts, parse_fallback_used = _extract_json_object(completed.stdout)
    if "error" in response and response["error"]:
        raise RuntimeError(f"Worker returned error: {response['error']}")

    result_payload = response.get("result_payload")
    if not isinstance(result_payload, dict):
        raise RuntimeError("Worker response missing object field: result_payload")

    worker_meta = response.get("worker_meta")
    if not isinstance(worker_meta, dict):
        worker_meta = {}
    worker_meta.setdefault("client_json_parse_attempts", parse_attempts)
    worker_meta.setdefault("client_raw_parse_fallback_used", parse_fallback_used)

    return result_payload, worker_meta
