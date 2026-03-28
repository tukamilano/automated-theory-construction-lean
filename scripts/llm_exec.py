from __future__ import annotations

import os
import subprocess
from pathlib import Path


def resolve_provider(explicit: str | None, *, env_name: str = "ATC_LLM_PROVIDER", default: str = "codex") -> str:
    provider = (explicit or os.getenv(env_name) or default).strip().lower()
    return provider or default


def build_exec_command(
    *,
    provider: str,
    sandbox: str,
    model: str | None = None,
    output_schema_path: Path | None = None,
    output_last_message_path: Path | None = None,
) -> list[str]:
    normalized = provider.strip().lower()
    if normalized == "codex":
        cmd = [
            "codex",
            "exec",
            "-",
            "--sandbox",
            sandbox,
            "--skip-git-repo-check",
        ]
        if output_schema_path is not None:
            cmd.extend(["--output-schema", str(output_schema_path)])
        if output_last_message_path is not None:
            cmd.extend(["--output-last-message", str(output_last_message_path)])
        if model:
            cmd.extend(["--model", model])
        return cmd

    raise ValueError(f"Unsupported LLM provider: {provider}")


def run_llm_exec(
    *,
    provider: str,
    prompt: str,
    sandbox: str,
    model: str | None = None,
    cwd: Path | str | None = None,
    output_schema_path: Path | None = None,
    output_last_message_path: Path | None = None,
    timeout_sec: int | None = None,
    capture_output: bool = True,
) -> subprocess.CompletedProcess[str]:
    cmd = build_exec_command(
        provider=provider,
        sandbox=sandbox,
        model=model,
        output_schema_path=output_schema_path,
        output_last_message_path=output_last_message_path,
    )
    return subprocess.run(
        cmd,
        input=prompt,
        capture_output=capture_output,
        text=True,
        timeout=timeout_sec,
        cwd=None if cwd is None else str(cwd),
        check=False,
    )
