from __future__ import annotations

import re
from pathlib import Path
from typing import Any

from common import write_json_atomic


DEFAULT_RESEARCH_AGENDA_PATH = Path("AutomatedTheoryConstruction/research_agenda.md")
DEFAULT_RESEARCH_AGENDA_JSON_PATH = Path("AutomatedTheoryConstruction/research_agenda.json")
LEGACY_RESEARCH_AGENDA_PATH = Path("research_agenda.md")

_SECTION_KEY_BY_HEADING = {
    "main objects": "main_objects",
    "main phenomena": "main_phenomena",
    "themes": "themes",
    "valued problem types": "valued_problem_types",
    "anti-goals": "what_does_not_count_as_progress",
    "what does not count as progress": "what_does_not_count_as_progress",
    "canonical targets": "canonical_targets",
    "soft constraints": "soft_constraints",
}
_SECTION_KEYS = tuple(_SECTION_KEY_BY_HEADING.values())
_BULLET_PREFIX_PATTERN = re.compile(r"^(?:[-*+]\s+|\d+\.\s+)")
_HEADING_PATTERN = re.compile(r"^\s{0,3}#{2,6}\s+(.+?)\s*$")
_NUMBERED_HEADING_PREFIX_PATTERN = re.compile(r"^\s*\d+(?:\.\d+)*[.)]?\s+")
_SURROUNDING_STRONG_PATTERN = re.compile(r"^\*\*(.+?)\*\*$")


def empty_research_agenda() -> dict[str, Any]:
    payload: dict[str, Any] = {
        "title": "",
        "introduction": "",
    }
    for key in _SECTION_KEYS:
        payload[key] = []
    return payload


def _normalize_section_item(line: str) -> str:
    stripped = line.strip()
    if not stripped:
        return ""
    normalized = _BULLET_PREFIX_PATTERN.sub("", stripped).strip()
    strong_match = _SURROUNDING_STRONG_PATTERN.match(normalized)
    if strong_match:
        normalized = strong_match.group(1).strip()
    return normalized


def _normalize_heading(line: str) -> str:
    normalized = line.strip().lower()
    normalized = _NUMBERED_HEADING_PREFIX_PATTERN.sub("", normalized)
    return normalized


def _agenda_json_path(markdown_path: Path) -> Path:
    if markdown_path.suffix.lower() == ".md":
        return markdown_path.with_suffix(".json")
    return markdown_path.parent / f"{markdown_path.name}.json"


def _append_item(items: list[str], current_item_lines: list[str], seen: set[str]) -> None:
    if not current_item_lines:
        return
    item = " ".join(line.strip() for line in current_item_lines if line.strip()).strip()
    if not item:
        return
    normalized = " ".join(item.split()).lower()
    if normalized in seen:
        return
    seen.add(normalized)
    items.append(item)


def parse_research_agenda_markdown(text: str) -> dict[str, Any]:
    payload = empty_research_agenda()
    if not text.strip():
        return payload

    raw_sections: dict[str, list[str]] = {key: [] for key in _SECTION_KEYS}
    current_section: str | None = None
    intro_lines: list[str] = []
    seen_first_section = False

    for line in text.splitlines():
        if not payload["title"]:
            stripped = line.strip()
            if stripped.startswith("# "):
                payload["title"] = stripped[2:].strip()
                current_section = None
                continue
        heading_match = _HEADING_PATTERN.match(line)
        if heading_match:
            raw_heading = heading_match.group(1).strip()
            normalized_heading = _normalize_heading(raw_heading)
            current_section = _SECTION_KEY_BY_HEADING.get(normalized_heading)
            if current_section is not None:
                seen_first_section = True
            continue
        if current_section is not None:
            raw_sections[current_section].append(line)
            continue
        if payload["title"] and not seen_first_section:
            if line.strip():
                intro_lines.append(line.strip())

    payload["introduction"] = " ".join(intro_lines).strip()

    for key, lines in raw_sections.items():
        items: list[str] = []
        seen: set[str] = set()
        current_item_lines: list[str] = []
        for line in lines:
            stripped = line.strip()
            if not stripped:
                if current_item_lines:
                    _append_item(items, current_item_lines, seen)
                    current_item_lines = []
                continue
            if _BULLET_PREFIX_PATTERN.match(stripped):
                if current_item_lines:
                    _append_item(items, current_item_lines, seen)
                item = _normalize_section_item(line)
                current_item_lines = [item] if item else []
                continue
            if current_item_lines:
                current_item_lines.append(stripped)
        if current_item_lines:
            _append_item(items, current_item_lines, seen)
        payload[key] = items

    return payload


def write_research_agenda_json(markdown_path: Path, payload: dict[str, Any]) -> Path:
    json_path = _agenda_json_path(markdown_path)
    write_json_atomic(json_path, payload)
    return json_path


def sync_research_agenda_json(markdown_path: Path) -> dict[str, Any]:
    payload = parse_research_agenda_markdown(markdown_path.read_text(encoding="utf-8"))
    write_research_agenda_json(markdown_path, payload)
    return payload


def load_research_agenda(path: Path) -> dict[str, Any]:
    candidate_paths = [path]
    if path == DEFAULT_RESEARCH_AGENDA_PATH or path.as_posix().endswith(DEFAULT_RESEARCH_AGENDA_PATH.as_posix()):
        candidate_paths.append(path.parent.parent / LEGACY_RESEARCH_AGENDA_PATH)
    for candidate in candidate_paths:
        if not candidate.exists():
            continue
        try:
            payload = parse_research_agenda_markdown(candidate.read_text(encoding="utf-8"))
            write_research_agenda_json(candidate, payload)
            return payload
        except Exception:
            continue
    return empty_research_agenda()


def format_research_agenda_prompt_block(research_agenda: dict[str, Any] | None) -> str:
    summary = summarize_research_agenda_for_state(research_agenda)
    if not summary:
        return ""

    section_labels = (
        ("main_objects", "Main objects"),
        ("main_phenomena", "Main phenomena"),
        ("themes", "Themes"),
        ("valued_problem_types", "Valued problem types"),
        ("what_does_not_count_as_progress", "What does not count as progress"),
        ("canonical_targets", "Canonical targets"),
        ("soft_constraints", "Soft constraints"),
    )
    lines = [
        "- Research agenda: treat the following as external value guidance for what kinds of problems count as meaningful progress.",
        "- Keep the agenda's main object families and main phenomena explicit when selecting or generating problems.",
        "- Treat this agenda as primary guidance when judging what counts as meaningful progress.",
        "- Use this agenda to prefer summary-changing, structurally central problems over safe peripheral extensions.",
        "- This agenda is a strong preference, not a hard constraint; still reject duplicates, shallow restatements, and mathematically weak proposals.",
    ]
    for key, label in section_labels:
        values = [str(item).strip() for item in summary.get(key, []) if str(item).strip()]
        if values:
            lines.append(f"- {label}: {'; '.join(values[:4])}")
    return "\n".join(lines) + "\n"


def summarize_research_agenda_for_state(research_agenda: dict[str, Any] | None) -> dict[str, list[str]]:
    agenda = dict(research_agenda or {})
    summary: dict[str, list[str]] = {}
    for key in _SECTION_KEYS:
        values = [str(item).strip() for item in agenda.get(key, []) if str(item).strip()]
        if values:
            summary[key] = values[:4]
    return summary
