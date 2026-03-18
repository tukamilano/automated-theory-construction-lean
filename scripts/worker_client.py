from __future__ import annotations

import json
import os
import shlex
import subprocess
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


def _extract_json_object(text: str) -> dict[str, Any]:
    raw = text.strip()
    if not raw:
        raise ValueError("Worker response is empty")

    try:
        payload = json.loads(raw)
        if isinstance(payload, dict):
            return payload
    except json.JSONDecodeError:
        pass

    start = raw.find("{")
    end = raw.rfind("}")
    if start == -1 or end == -1 or end <= start:
        raise ValueError("Worker response did not contain a JSON object")

    payload = json.loads(raw[start : end + 1])
    if not isinstance(payload, dict):
        raise ValueError("Worker JSON payload must be an object")
    return payload


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

    response = _extract_json_object(completed.stdout)
    if "error" in response and response["error"]:
        raise RuntimeError(f"Worker returned error: {response['error']}")

    result_payload = response.get("result_payload")
    if not isinstance(result_payload, dict):
        raise RuntimeError("Worker response missing object field: result_payload")

    worker_meta = response.get("worker_meta")
    if not isinstance(worker_meta, dict):
        worker_meta = {}

    return result_payload, worker_meta
