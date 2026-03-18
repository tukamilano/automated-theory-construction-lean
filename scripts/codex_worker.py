from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def _extract_json_object(text: str) -> dict[str, Any]:
    raw = text.strip()
    if not raw:
        raise ValueError("empty model output")

    try:
        payload = json.loads(raw)
        if isinstance(payload, dict):
            return payload
    except json.JSONDecodeError:
        pass

    start = raw.find("{")
    end = raw.rfind("}")
    if start == -1 or end == -1 or end <= start:
        raise ValueError("model output did not contain a JSON object")

    payload = json.loads(raw[start : end + 1])
    if not isinstance(payload, dict):
        raise ValueError("model output JSON must be an object")
    return payload


def _build_prompt(task_type: str, system_prompt: str, payload: dict[str, Any]) -> str:
    return (
        "You are a strict JSON worker. Return only one JSON object and no markdown.\n"
        f"Task type: {task_type}\n\n"
        "System instructions (must follow):\n"
        f"{system_prompt}\n\n"
        "Input payload JSON:\n"
        f"{json.dumps(payload, ensure_ascii=False, indent=2)}\n\n"
        "Output requirements:\n"
        "- Return exactly one JSON object for the task response.\n"
        "- Do not add explanation text.\n"
    )


def _run_codex(prompt: str, timeout_sec: int) -> str:
    model = (os.getenv("ATC_CODEX_MODEL") or "").strip()
    cmd: list[str] = [
        "codex",
        "exec",
        "-",
        "--sandbox",
        "read-only",
        "--skip-git-repo-check",
    ]
    if model:
        cmd.extend(["--model", model])

    with tempfile.NamedTemporaryFile(mode="w+", encoding="utf-8", delete=False) as handle:
        output_path = Path(handle.name)

    cmd.extend(["--output-last-message", str(output_path)])

    try:
        completed = subprocess.run(
            cmd,
            input=prompt,
            capture_output=True,
            text=True,
            timeout=timeout_sec,
            check=False,
        )
        if completed.returncode != 0:
            stderr = (completed.stderr or "").strip()
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

        if task_type not in {"picker", "prover", "repair"}:
            raise ValueError(f"unsupported task_type: {task_type}")

        outer_timeout = int((os.getenv("ATC_WORKER_TIMEOUT") or "180").strip())
        codex_timeout_text = (os.getenv("ATC_CODEX_TIMEOUT") or "").strip()
        # Keep inner timeout slightly below outer timeout to avoid subprocess timeout races.
        timeout_sec = int(codex_timeout_text) if codex_timeout_text else max(30, outer_timeout - 10)
        prompt = _build_prompt(task_type=task_type, system_prompt=system_prompt, payload=payload)
        model_output = _run_codex(prompt=prompt, timeout_sec=timeout_sec)
        result_payload = _extract_json_object(model_output)

        response = {
            "result_payload": result_payload,
            "worker_meta": {
                "worker": "codex_worker",
                "task_type": task_type,
                "model": (os.getenv("ATC_CODEX_MODEL") or "").strip(),
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
