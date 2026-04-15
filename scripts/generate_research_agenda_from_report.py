from __future__ import annotations

import argparse
import os
import re
import sys
import tempfile
from pathlib import Path

from atc_config import REPO_ROOT
from llm_exec import resolve_provider
from llm_exec import run_llm_exec
from prompt_loader import load_prompt_file
from research_agenda import DEFAULT_RESEARCH_AGENDA_PATH
from research_agenda import parse_research_agenda_markdown
from research_agenda import write_research_agenda_json


DEFAULT_SYSTEM_PROMPT = Path("prompts/research_agenda/system.md")
DEFAULT_USER_PROMPT = Path("prompts/research_agenda/user_template.md")
DEFAULT_OUTPUT = DEFAULT_RESEARCH_AGENDA_PATH

DEFAULT_LOCAL_PREFERENCES = [
    "Keep the writing severe and compact.",
    "Prefer structural distinctions, exact boundaries, classification goals, and metatheoretic pressure.",
    "Use anti-goals aggressively to rule out shallow or fashionable directions.",
    "Make the canonical targets feel genuinely summary-changing.",
    "Preserve exact section headings and put all essential content into bullet or numbered-list items so the result can be reused directly as `research_agenda.md`.",
]

SECTION_ORDER = (
    ("main_objects", "Main Objects"),
    ("main_phenomena", "Main Phenomena"),
    ("themes", "Themes"),
    ("valued_problem_types", "Valued Problem Types"),
    ("what_does_not_count_as_progress", "What Does Not Count As Progress"),
    ("canonical_targets", "Canonical Targets"),
    ("soft_constraints", "Soft Constraints"),
)


def _extract_report_title(report_text: str, fallback: str) -> str:
    for raw_line in report_text.splitlines():
        stripped = raw_line.strip()
        if not stripped:
            continue
        if stripped.startswith("#"):
            candidate = stripped.lstrip("#").strip()
            candidate = re.sub(r"^\*+|\*+$", "", candidate).strip()
            if candidate:
                return candidate
        break
    return fallback


def _infer_field(title: str) -> str:
    lowered = title.lower()
    if "lambek" in lowered:
        return "The Lambek calculus and its structural theory"
    return title


def _style_anchor_block(path: Path | None) -> str:
    if path is None:
        return "No existing agenda is provided. Infer the style from the system instructions alone."
    if not path.exists():
        return f"No existing agenda is available at `{path}`. Infer the style from the system instructions alone."
    text = path.read_text(encoding="utf-8").strip()
    if not text:
        return f"The style anchor file `{path}` is empty. Infer the style from the system instructions alone."
    return (
        f"Match the tone and strictness of this existing agenda from `{path}`. "
        "Use it only as a style anchor, not as content to paraphrase.\n\n"
        f"{text}"
    )


def _local_preferences_block(items: list[str]) -> str:
    cleaned = [item.strip() for item in items if item.strip()]
    if not cleaned:
        cleaned = list(DEFAULT_LOCAL_PREFERENCES)
    return "\n".join(f"- {item}" for item in cleaned)


def render_user_prompt(
    *,
    template_text: str,
    title: str,
    field: str,
    report_text: str,
    style_anchor_text: str,
    local_preferences: list[str],
) -> str:
    rendered = template_text
    rendered = rendered.replace("<TITLE>", title.strip())
    rendered = rendered.replace("<FIELD>", field.strip())
    rendered = rendered.replace("<STYLE_ANCHOR_BLOCK>", style_anchor_text.strip())
    rendered = rendered.replace("<LOCAL_PREFERENCES_BLOCK>", _local_preferences_block(local_preferences))
    rendered = rendered.replace("<REPORT>", report_text.rstrip())
    return rendered


def build_full_prompt(*, system_prompt: str, user_prompt: str) -> str:
    return (
        "System instructions (must follow):\n"
        f"{system_prompt.rstrip()}\n\n"
        "User request:\n"
        f"{user_prompt.rstrip()}\n"
    )


def validate_generated_agenda(text: str) -> None:
    if not text.strip():
        raise ValueError("generated agenda is empty")
    first_nonempty = next((line.strip() for line in text.splitlines() if line.strip()), "")
    if not first_nonempty.startswith("# Research Agenda"):
        raise ValueError("generated agenda must start with a `# Research Agenda ...` title")
    payload = parse_research_agenda_markdown(text)
    missing = [label for key, label in SECTION_ORDER if not payload.get(key)]
    if missing:
        raise ValueError(f"generated agenda is missing required section items: {', '.join(missing)}")


def write_text_atomic(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    content = text if text.endswith("\n") else text + "\n"
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=str(path.parent), delete=False) as handle:
        handle.write(content)
        tmp_path = Path(handle.name)
    os.replace(tmp_path, path)


def run_generation(
    *,
    report_file: Path,
    output_file: Path,
    system_prompt_file: Path,
    user_prompt_file: Path,
    title: str | None,
    field: str | None,
    style_anchor_file: Path | None,
    local_preferences: list[str],
    provider: str,
    model: str | None,
    sandbox: str,
    timeout_sec: int | None,
    prompt_output_file: Path | None,
) -> str:
    if not report_file.exists():
        raise FileNotFoundError(f"report file not found: {report_file}")
    if not system_prompt_file.exists():
        raise FileNotFoundError(f"system prompt file not found: {system_prompt_file}")
    if not user_prompt_file.exists():
        raise FileNotFoundError(f"user prompt file not found: {user_prompt_file}")

    report_text = report_file.read_text(encoding="utf-8").strip()
    if not report_text:
        raise ValueError(f"report file is empty: {report_file}")

    resolved_title = (title or "").strip() or _extract_report_title(report_text, fallback=report_file.stem)
    resolved_field = (field or "").strip() or _infer_field(resolved_title)
    style_anchor_path = style_anchor_file
    if style_anchor_path is None and output_file.exists():
        style_anchor_path = output_file

    system_prompt = load_prompt_file(system_prompt_file)
    user_template = load_prompt_file(user_prompt_file)
    user_prompt = render_user_prompt(
        template_text=user_template,
        title=resolved_title,
        field=resolved_field,
        report_text=report_text,
        style_anchor_text=_style_anchor_block(style_anchor_path),
        local_preferences=local_preferences,
    )
    full_prompt = build_full_prompt(system_prompt=system_prompt, user_prompt=user_prompt)

    if prompt_output_file is not None:
        write_text_atomic(prompt_output_file, full_prompt)

    with tempfile.NamedTemporaryFile("w+", encoding="utf-8", delete=False) as handle:
        output_last_message_path = Path(handle.name)

    try:
        completed = run_llm_exec(
            provider=provider,
            prompt=full_prompt,
            sandbox=sandbox,
            model=model,
            cwd=REPO_ROOT,
            output_last_message_path=output_last_message_path,
            timeout_sec=timeout_sec,
        )
        if completed.returncode != 0:
            stderr = (completed.stderr or "").strip()
            stdout = (completed.stdout or "").strip()
            details = stderr or stdout or f"{provider} exec failed with code {completed.returncode}"
            raise RuntimeError(details)

        generated_text = output_last_message_path.read_text(encoding="utf-8").strip()
        if not generated_text:
            generated_text = (completed.stdout or "").strip()
        validate_generated_agenda(generated_text)
        write_text_atomic(output_file, generated_text)
        write_research_agenda_json(output_file, parse_research_agenda_markdown(generated_text))
        return generated_text
    finally:
        try:
            output_last_message_path.unlink(missing_ok=True)
        except OSError:
            pass


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate AutomatedTheoryConstruction/research_agenda.md from a deep research report."
    )
    parser.add_argument("--report-file", required=True)
    parser.add_argument("--output-file", default=str(DEFAULT_OUTPUT))
    parser.add_argument("--system-prompt-file", default=str(DEFAULT_SYSTEM_PROMPT))
    parser.add_argument("--user-prompt-file", default=str(DEFAULT_USER_PROMPT))
    parser.add_argument("--title")
    parser.add_argument("--field")
    parser.add_argument("--style-anchor-file")
    parser.add_argument("--local-preference", action="append", default=[])
    parser.add_argument("--provider")
    parser.add_argument("--model")
    parser.add_argument("--sandbox", default="read-only")
    parser.add_argument("--timeout-sec", type=int)
    parser.add_argument("--prompt-output-file")
    parser.add_argument("--preview-prompt", action="store_true")
    parser.add_argument("--print-output", action="store_true")
    args = parser.parse_args()

    provider = resolve_provider(args.provider)
    report_file = Path(args.report_file)
    output_file = Path(args.output_file)
    system_prompt_file = Path(args.system_prompt_file)
    user_prompt_file = Path(args.user_prompt_file)
    style_anchor_file = Path(args.style_anchor_file) if args.style_anchor_file else None
    prompt_output_file = Path(args.prompt_output_file) if args.prompt_output_file else None

    if args.preview_prompt:
        try:
            report_text = report_file.read_text(encoding="utf-8").strip()
            resolved_title = (args.title or "").strip() or _extract_report_title(report_text, fallback=report_file.stem)
            resolved_field = (args.field or "").strip() or _infer_field(resolved_title)
            style_anchor_path = style_anchor_file
            if style_anchor_path is None and output_file.exists():
                style_anchor_path = output_file
            full_prompt = build_full_prompt(
                system_prompt=load_prompt_file(system_prompt_file),
                user_prompt=render_user_prompt(
                    template_text=load_prompt_file(user_prompt_file),
                    title=resolved_title,
                    field=resolved_field,
                    report_text=report_text,
                    style_anchor_text=_style_anchor_block(style_anchor_path),
                    local_preferences=args.local_preference,
                ),
            )
            if prompt_output_file is not None:
                write_text_atomic(prompt_output_file, full_prompt)
        except Exception as exc:
            print(f"generate_research_agenda_from_report.py: error: {exc}", file=sys.stderr, flush=True)
            return 1
        print(full_prompt)
        return 0

    try:
        generated_text = run_generation(
            report_file=report_file,
            output_file=output_file,
            system_prompt_file=system_prompt_file,
            user_prompt_file=user_prompt_file,
            title=args.title,
            field=args.field,
            style_anchor_file=style_anchor_file,
            local_preferences=args.local_preference,
            provider=provider,
            model=args.model,
            sandbox=args.sandbox,
            timeout_sec=args.timeout_sec,
            prompt_output_file=prompt_output_file,
        )
    except Exception as exc:
        print(f"generate_research_agenda_from_report.py: error: {exc}", file=sys.stderr, flush=True)
        return 1

    print(f"Wrote {output_file}", file=sys.stderr, flush=True)
    if args.print_output:
        print(generated_text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
