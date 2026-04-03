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
    timeout_sec: int | None
    propagate_timeout: bool


def _single_line_excerpt(text: str, limit: int = 240) -> str:
    normalized = " ".join(text.strip().split())
    if not normalized:
        return ""
    if len(normalized) <= limit:
        return normalized
    return normalized[: limit - 3] + "..."


def _resolve_timeout_seconds(timeout_text: str | None, default: int | None) -> int | None:
    raw = (timeout_text or "").strip()
    if not raw:
        return default
    parsed = int(raw)
    if parsed == 0:
        return None
    return parsed


def load_worker_settings(
    command_override: str | None,
    timeout_override: int | None,
    default_timeout_sec: int | None = 180,
) -> WorkerSettings:
    command = (command_override or os.getenv("ATC_WORKER_COMMAND") or "").strip()
    timeout_env_text = os.getenv("ATC_WORKER_TIMEOUT")
    timeout_from_env = _resolve_timeout_seconds(timeout_env_text, default_timeout_sec)
    timeout_sec = (
        None if timeout_override == 0 else timeout_override
    ) if timeout_override is not None else timeout_from_env
    propagate_timeout = timeout_override is not None or bool((timeout_env_text or "").strip())

    if not command:
        raise ValueError("Worker command is required. Set --worker-command or ATC_WORKER_COMMAND.")
    if timeout_sec is not None and timeout_sec <= 0:
        raise ValueError("Worker timeout must be > 0 seconds.")

    return WorkerSettings(
        command=command,
        timeout_sec=timeout_sec,
        propagate_timeout=propagate_timeout,
    )


def load_task_worker_settings(
    *,
    task_name: str,
    base_settings: WorkerSettings,
    command_override: str | None = None,
    timeout_override: int | None = None,
) -> WorkerSettings:
    env_prefix = f"ATC_{task_name.upper()}_WORKER"
    timeout_env_text = os.getenv(f"{env_prefix}_TIMEOUT")
    command = (
        command_override
        or os.getenv(f"{env_prefix}_COMMAND")
        or base_settings.command
    ).strip()
    timeout_from_env = _resolve_timeout_seconds(
        timeout_env_text,
        base_settings.timeout_sec,
    )
    timeout_sec = (
        None if timeout_override == 0 else timeout_override
    ) if timeout_override is not None else timeout_from_env
    propagate_timeout = (
        timeout_override is not None
        or bool((timeout_env_text or "").strip())
        or base_settings.propagate_timeout
    )

    if not command:
        raise ValueError(f"{task_name} worker command must not be empty.")
    if timeout_sec is not None and timeout_sec <= 0:
        raise ValueError(f"{task_name} worker timeout must be > 0 seconds.")

    return WorkerSettings(
        command=command,
        timeout_sec=timeout_sec,
        propagate_timeout=propagate_timeout,
    )


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

    worker_env = os.environ.copy()
    if settings.propagate_timeout:
        worker_env[f"ATC_{task_type.upper()}_WORKER_TIMEOUT"] = (
            "0" if settings.timeout_sec is None else str(settings.timeout_sec)
        )

    try:
        completed = subprocess.run(
            cmd,
            input=json.dumps(request_body, ensure_ascii=False),
            capture_output=True,
            text=True,
            timeout=settings.timeout_sec,
            env=worker_env,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        timeout_label = f"{settings.timeout_sec}s" if settings.timeout_sec is not None else "without a limit"
        stderr_excerpt = _single_line_excerpt(
            (exc.stderr.decode() if isinstance(exc.stderr, bytes) else exc.stderr) or ""
        )
        stdout_excerpt = _single_line_excerpt(
            (exc.stdout.decode() if isinstance(exc.stdout, bytes) else exc.stdout) or ""
        )
        detail_parts: list[str] = []
        if stderr_excerpt:
            detail_parts.append(f"stderr={stderr_excerpt}")
        if stdout_excerpt:
            detail_parts.append(f"stdout={stdout_excerpt}")
        detail_suffix = f" ({'; '.join(detail_parts)})" if detail_parts else ""
        raise RuntimeError(
            f"Worker call timed out after {timeout_label}. "
            "This timeout applies to one worker subprocess invocation, not a whole retry loop. "
            "Try increasing --worker-timeout (or ATC_WORKER_TIMEOUT), e.g. 180-300."
            f"{detail_suffix}"
        ) from exc

    if completed.returncode != 0:
        stderr = (completed.stderr or "").strip()
        raise RuntimeError(f"Worker exited with code {completed.returncode}: {stderr}")

    response, parse_attempts, parse_fallback_used = _extract_json_object(completed.stdout)
    if "error" in response and response["error"]:
        error_details: list[str] = []
        raw_worker_meta = response.get("worker_meta")
        if isinstance(raw_worker_meta, dict):
            task_name = raw_worker_meta.get("task_type")
            if isinstance(task_name, str) and task_name.strip():
                error_details.append(f"task_type={task_name}")
            if raw_worker_meta.get("contract_retry_used"):
                error_details.append("contract_retry_used=true")

            initial_excerpt = raw_worker_meta.get("initial_raw_model_output_excerpt")
            if isinstance(initial_excerpt, str) and initial_excerpt.strip():
                error_details.append(
                    f"initial_output_excerpt={_single_line_excerpt(initial_excerpt)}"
                )

            retry_excerpt = raw_worker_meta.get("raw_model_output_excerpt")
            if isinstance(retry_excerpt, str) and retry_excerpt.strip():
                error_details.append(
                    f"retry_output_excerpt={_single_line_excerpt(retry_excerpt)}"
                )

        detail_suffix = f" ({'; '.join(error_details)})" if error_details else ""
        raise RuntimeError(f"Worker returned error: {response['error']}{detail_suffix}")

    result_payload = response.get("result_payload")
    if not isinstance(result_payload, dict):
        raise RuntimeError("Worker response missing object field: result_payload")

    worker_meta = response.get("worker_meta")
    if not isinstance(worker_meta, dict):
        worker_meta = {}
    worker_meta.setdefault("client_json_parse_attempts", parse_attempts)
    worker_meta.setdefault("client_raw_parse_fallback_used", parse_fallback_used)

    return result_payload, worker_meta
