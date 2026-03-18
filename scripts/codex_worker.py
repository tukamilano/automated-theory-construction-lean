from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


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
        raise ValueError("empty model output")

    parse_attempts = 0

    try:
        parse_attempts += 1
        payload = json.loads(raw)
        if isinstance(payload, dict):
            return payload, parse_attempts, False
    except json.JSONDecodeError:
        pass

    # Try explicit fenced json snippets first (common in interactive responses).
    fenced_blocks = re.findall(r"```json\s*(\{.*?\})\s*```", raw, flags=re.DOTALL | re.IGNORECASE)
    for block in fenced_blocks:
        try:
            parse_attempts += 1
            payload = json.loads(block)
            if isinstance(payload, dict):
                return payload, parse_attempts, True
        except json.JSONDecodeError:
            continue

    # Fallback to scanning for balanced JSON-object candidates.
    for candidate in _iter_braced_json_candidates(raw):
        try:
            parse_attempts += 1
            payload = json.loads(candidate)
            if isinstance(payload, dict):
                return payload, parse_attempts, True
        except json.JSONDecodeError:
            continue

    raise ValueError("model output did not contain a parseable JSON object")


def _build_prompt(task_type: str, system_prompt: str, payload: dict[str, Any]) -> str:
    return (
        "You are an interactive worker in an automated theorem-construction loop.\n"
        f"Task type: {task_type}\n\n"
        "System instructions (must follow):\n"
        f"{system_prompt}\n\n"
        "Input payload JSON:\n"
        f"{json.dumps(payload, ensure_ascii=False, indent=2)}\n\n"
        "Output contract:\n"
        "- You may think and explain briefly in natural language.\n"
        "- The final answer must include one task-response JSON object.\n"
        "- Ensure the last JSON object in your final answer is the task-response payload.\n"
    )


def _run_codex(prompt: str, timeout_sec: int) -> str:
    model = (os.getenv("ATC_CODEX_MODEL") or "").strip()
    base_cmd: list[str] = [
        "codex",
        "exec",
        "-",
        "--sandbox",
        "read-only",
        "--skip-git-repo-check",
    ]

    def build_cmd(use_model: bool) -> list[str]:
        cmd = list(base_cmd)
        if use_model and model:
            cmd.extend(["--model", model])
        return cmd

    with tempfile.NamedTemporaryFile(mode="w+", encoding="utf-8", delete=False) as handle:
        output_path = Path(handle.name)

    try:
        def run_once(use_model: bool) -> subprocess.CompletedProcess[str]:
            cmd = build_cmd(use_model)
            cmd.extend(["--output-last-message", str(output_path)])
            return subprocess.run(
                cmd,
                input=prompt,
                capture_output=True,
                text=True,
                timeout=timeout_sec,
                check=False,
            )

        completed = run_once(use_model=True)
        if completed.returncode != 0:
            stderr = (completed.stderr or "").strip()
            unsupported_model = (
                model
                and "not supported" in stderr.lower()
                and "model" in stderr.lower()
            )
            if unsupported_model:
                completed = run_once(use_model=False)
                if completed.returncode != 0:
                    retry_stderr = (completed.stderr or "").strip()
                    raise RuntimeError(f"codex exec failed ({completed.returncode}): {retry_stderr}")
            else:
                raise RuntimeError(f"codex exec failed ({completed.returncode}): {stderr}")

        text = output_path.read_text(encoding="utf-8") if output_path.exists() else ""
        if not text.strip():
            text = (completed.stdout or "").strip()
        return text
    finally:
        try:
            output_path.unlink(missing_ok=True)
        except OSError:
            pass


def main() -> None:
    response: dict[str, Any]
    try:
        raw = sys.stdin.read()
        request = json.loads(raw)
        if not isinstance(request, dict):
            raise ValueError("worker request must be a JSON object")

        task_type = str(request.get("task_type", "")).strip()
        system_prompt = str(request.get("system_prompt", ""))
        payload = request.get("payload", {})
        if not isinstance(payload, dict):
            raise ValueError("payload must be a JSON object")

        if task_type not in {"picker", "prover", "repair", "expand"}:
            raise ValueError(f"unsupported task_type: {task_type}")

        outer_timeout = int((os.getenv("ATC_WORKER_TIMEOUT") or "180").strip())
        codex_timeout_text = (os.getenv("ATC_CODEX_TIMEOUT") or "").strip()
        # Keep inner timeout slightly below outer timeout to avoid subprocess timeout races.
        timeout_sec = int(codex_timeout_text) if codex_timeout_text else max(30, outer_timeout - 10)
        prompt = _build_prompt(task_type=task_type, system_prompt=system_prompt, payload=payload)
        model_output = _run_codex(prompt=prompt, timeout_sec=timeout_sec)
        result_payload, parse_attempts, used_fallback = _extract_json_object(model_output)

        response = {
            "result_payload": result_payload,
            "worker_meta": {
                "worker": "codex_worker",
                "task_type": task_type,
                "model": (os.getenv("ATC_CODEX_MODEL") or "").strip(),
                "json_parse_attempts": parse_attempts,
                "raw_parse_fallback_used": used_fallback,
                "raw_output_chars": len(model_output),
            },
            "error": None,
        }
    except Exception as exc:
        response = {
            "result_payload": {},
            "worker_meta": {"worker": "codex_worker"},
            "error": str(exc),
        }

    sys.stdout.write(json.dumps(response, ensure_ascii=False))


if __name__ == "__main__":
    main()
