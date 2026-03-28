from __future__ import annotations

import os
import subprocess
from pathlib import Path


DEFAULT_PROVIDER_MODELS: dict[str, str] = {
    "codex": "gpt-5.4",
    "claude": "sonnet",
}


def resolve_provider(explicit: str | None, *, env_name: str = "ATC_LLM_PROVIDER", default: str = "codex") -> str:
    provider = (explicit or os.getenv(env_name) or default).strip().lower()
    return provider or default


def resolve_model(provider: str, explicit: str | None) -> str | None:
    model = (explicit or "").strip()
    if model:
        return model
    return DEFAULT_PROVIDER_MODELS.get(provider.strip().lower())


def _sandbox_tools_for_claude(sandbox: str) -> list[str]:
    normalized = sandbox.strip().lower()
    if normalized == "workspace-write":
        return ["Read", "Edit", "Write", "Glob", "Grep", "Bash"]
    return ["Read", "Glob", "Grep"]


def build_exec_command(
    *,
    provider: str,
    sandbox: str,
    model: str | None = None,
    output_schema_path: Path | None = None,
    output_last_message_path: Path | None = None,
    cwd: Path | None = None,
) -> list[str]:
    normalized = provider.strip().lower()
    resolved_model = resolve_model(normalized, model)
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
        if resolved_model:
            cmd.extend(["--model", resolved_model])
        return cmd

    if normalized == "claude":
        cmd = [
            "claude",
            "--print",
            "--output-format",
            "text",
            "--permission-mode",
            "bypassPermissions" if sandbox.strip().lower() == "workspace-write" else "dontAsk",
            "--setting-sources",
            "project,local,user",
            "--allowedTools",
            ",".join(_sandbox_tools_for_claude(sandbox)),
        ]
        if sandbox.strip().lower() == "workspace-write":
            cmd.append("--dangerously-skip-permissions")
        if cwd is not None:
            cmd.extend(["--add-dir", str(cwd)])
        if output_schema_path is not None:
            schema = (
                output_schema_path.read_text(encoding="utf-8")
                if output_schema_path.exists()
                else '{"type":"object"}'
            )
            cmd.extend(["--json-schema", schema])
        if resolved_model:
            cmd.extend(["--model", resolved_model])
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
    resolved_cwd = Path(cwd).resolve() if cwd is not None else Path.cwd().resolve()
    cmd = build_exec_command(
        provider=provider,
        sandbox=sandbox,
        model=model,
        output_schema_path=output_schema_path,
        output_last_message_path=output_last_message_path,
        cwd=resolved_cwd,
    )
    return subprocess.run(
        cmd,
        input=prompt,
        capture_output=capture_output,
        text=True,
        timeout=timeout_sec,
        cwd=str(resolved_cwd),
        check=False,
    )
