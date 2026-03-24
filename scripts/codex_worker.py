from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def _single_line_excerpt(text: str, limit: int = 400) -> str:
    normalized = " ".join(text.strip().split())
    if not normalized:
        return ""
    if len(normalized) <= limit:
        return normalized
    return normalized[: limit - 3] + "..."


def _task_env_key(task_type: str, suffix: str) -> str:
    return f"ATC_{task_type.upper()}_{suffix}"


def _resolve_task_env(task_type: str, suffix: str, default: str = "") -> str:
    task_override = (os.getenv(_task_env_key(task_type, suffix)) or "").strip()
    if task_override:
        return task_override
    return (os.getenv(f"ATC_{suffix}") or default).strip()


def _default_worker_timeout_for_task(task_type: str) -> int | None:
    if task_type == "refactor_derived":
        return None
    return 180


def _resolve_timeout_seconds(timeout_text: str | None, default: int | None) -> int | None:
    raw = (timeout_text or "").strip()
    if not raw:
        return default
    parsed = int(raw)
    if parsed == 0:
        return None
    return parsed


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
        "You are a non-interactive worker in an automated theorem-construction loop.\n"
        f"Task type: {task_type}\n\n"
        "System instructions (must follow):\n"
        f"{system_prompt}\n\n"
        "Input payload JSON:\n"
        f"{json.dumps(payload, ensure_ascii=False, indent=2)}\n\n"
        "Output contract:\n"
        "- Use English for any natural-language text you include.\n"
        "- Never ask clarifying questions or request user input.\n"
        "- If information is missing or ambiguous, make the best conservative inference and still return a valid task-response JSON object.\n"
        "- If you cannot solve the task, return the contract-compliant fallback for that task instead of a question.\n"
        "- The final answer must include one task-response JSON object.\n"
        "- Ensure the last JSON object in your final answer is the task-response payload.\n"
    )


def _build_contract_repair_prompt(
    task_type: str,
    system_prompt: str,
    payload: dict[str, Any],
    previous_output: str,
) -> str:
    return (
        _build_prompt(task_type=task_type, system_prompt=system_prompt, payload=payload)
        + "\nPrevious response violated the output contract.\n"
        + "Do not ask questions. Do not add explanations unless they are inside the required JSON fields.\n"
        + "Return exactly one valid task-response JSON object now.\n"
        + "If you remain uncertain, use the most conservative valid fallback (for example `stuck` or `[]`) instead of asking for clarification.\n\n"
        + "Previous invalid response:\n"
        + previous_output
        + "\n"
    )


def _run_codex(task_type: str, prompt: str, timeout_sec: int | None) -> tuple[str, str]:
    model = _resolve_task_env(task_type, "CODEX_MODEL")
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
        return text, model
    finally:
        try:
            output_path.unlink(missing_ok=True)
        except OSError:
            pass


def main() -> None:
    response: dict[str, Any]
    task_type = ""
    resolved_model = ""
    contract_retry_used = False
    initial_model_output = ""
    model_output = ""
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

        if task_type not in {"prover_statement", "prover", "formalize", "repair", "expand", "refactor_derived"}:
            raise ValueError(f"unsupported task_type: {task_type}")

        default_outer_timeout = _default_worker_timeout_for_task(task_type)
        default_outer_timeout_text = "" if default_outer_timeout is None else str(default_outer_timeout)
        outer_timeout = _resolve_timeout_seconds(
            _resolve_task_env(task_type, "WORKER_TIMEOUT", default_outer_timeout_text),
            default_outer_timeout,
        )
        codex_timeout_text = _resolve_task_env(task_type, "CODEX_TIMEOUT")
        codex_timeout = _resolve_timeout_seconds(codex_timeout_text, None)
        # Keep inner timeout slightly below outer timeout to avoid subprocess timeout races when both are bounded.
        if codex_timeout is not None:
            timeout_sec = codex_timeout
        elif outer_timeout is not None:
            timeout_sec = max(30, outer_timeout - 10)
        else:
            timeout_sec = None
        prompt = _build_prompt(task_type=task_type, system_prompt=system_prompt, payload=payload)
        model_output, resolved_model = _run_codex(task_type=task_type, prompt=prompt, timeout_sec=timeout_sec)
        try:
            result_payload, parse_attempts, used_fallback = _extract_json_object(model_output)
        except ValueError:
            contract_retry_used = True
            initial_model_output = model_output
            repair_prompt = _build_contract_repair_prompt(
                task_type=task_type,
                system_prompt=system_prompt,
                payload=payload,
                previous_output=model_output,
            )
            model_output, resolved_model = _run_codex(
                task_type=task_type,
                prompt=repair_prompt,
                timeout_sec=max(30, timeout_sec // 2) if timeout_sec is not None else None,
            )
            try:
                result_payload, parse_attempts, used_fallback = _extract_json_object(model_output)
            except ValueError as second_exc:
                excerpts: list[str] = []
                initial_excerpt = _single_line_excerpt(initial_model_output)
                retry_excerpt = _single_line_excerpt(model_output)
                if initial_excerpt:
                    excerpts.append(f"initial_output_excerpt={initial_excerpt}")
                if retry_excerpt:
                    excerpts.append(f"retry_output_excerpt={retry_excerpt}")
                detail = f"; {'; '.join(excerpts)}" if excerpts else ""
                raise ValueError(
                    "model output did not contain a parseable JSON object after contract retry"
                    f"{detail}"
                ) from second_exc

        response = {
            "result_payload": result_payload,
            "worker_meta": {
                "worker": "codex_worker",
                "task_type": task_type,
                "model": resolved_model,
                "json_parse_attempts": parse_attempts,
                "raw_parse_fallback_used": used_fallback,
                "raw_output_chars": len(model_output),
                "raw_model_output": model_output,
                "contract_retry_used": contract_retry_used,
            },
            "error": None,
        }
    except Exception as exc:
        worker_meta: dict[str, Any] = {"worker": "codex_worker"}
        if task_type:
            worker_meta["task_type"] = task_type
        if resolved_model:
            worker_meta["model"] = resolved_model
        if contract_retry_used:
            worker_meta["contract_retry_used"] = True
        initial_excerpt = _single_line_excerpt(initial_model_output)
        retry_excerpt = _single_line_excerpt(model_output)
        if initial_excerpt:
            worker_meta["initial_raw_model_output_excerpt"] = initial_excerpt
        if retry_excerpt:
            worker_meta["raw_model_output_excerpt"] = retry_excerpt
        response = {
            "result_payload": {},
            "worker_meta": worker_meta,
            "error": str(exc),
        }

    sys.stdout.write(json.dumps(response, ensure_ascii=False))


if __name__ == "__main__":
    main()
