from __future__ import annotations

import re
from pathlib import Path
from typing import Any


DEFAULT_RESEARCH_AGENDA_PATH = Path("AutomatedTheoryConstruction/research_agenda.md")
LEGACY_RESEARCH_AGENDA_PATH = Path("research_agenda.md")

_SECTION_KEY_BY_HEADING = {
    "themes": "themes",
    "valued problem types": "valued_problem_types",
    "anti-goals": "anti_goals",
    "canonical targets": "canonical_targets",
    "soft constraints": "soft_constraints",
}
_SECTION_KEYS = tuple(_SECTION_KEY_BY_HEADING.values())
_BULLET_PREFIX_PATTERN = re.compile(r"^(?:[-*+]\s+|\d+\.\s+)")
_HEADING_PATTERN = re.compile(r"^\s{0,3}#{2,6}\s+(.+?)\s*$")


def empty_research_agenda() -> dict[str, Any]:
    payload: dict[str, Any] = {}
    for key in _SECTION_KEYS:
        payload[key] = []
    return payload


def _normalize_section_item(line: str) -> str:
    stripped = line.strip()
    if not stripped:
        return ""
    return _BULLET_PREFIX_PATTERN.sub("", stripped).strip()


def parse_research_agenda_markdown(text: str) -> dict[str, Any]:
    payload = empty_research_agenda()
    if not text.strip():
        return payload

    raw_sections: dict[str, list[str]] = {key: [] for key in _SECTION_KEYS}
    current_section: str | None = None

    for line in text.splitlines():
        heading_match = _HEADING_PATTERN.match(line)
        if heading_match:
            heading = heading_match.group(1).strip().lower()
            current_section = _SECTION_KEY_BY_HEADING.get(heading)
            continue
        if current_section is not None:
            raw_sections[current_section].append(line)

    for key, lines in raw_sections.items():
        items: list[str] = []
        seen: set[str] = set()
        for line in lines:
            item = _normalize_section_item(line)
            if not item:
                continue
            normalized = " ".join(item.split()).lower()
            if normalized in seen:
                continue
            seen.add(normalized)
            items.append(item)
        payload[key] = items

    return payload


def load_research_agenda(path: Path) -> dict[str, Any]:
    candidate_paths = [path]
    if path == DEFAULT_RESEARCH_AGENDA_PATH or path.as_posix().endswith(DEFAULT_RESEARCH_AGENDA_PATH.as_posix()):
        candidate_paths.append(path.parent.parent / LEGACY_RESEARCH_AGENDA_PATH)
    for candidate in candidate_paths:
        if not candidate.exists():
            continue
        try:
            return parse_research_agenda_markdown(candidate.read_text(encoding="utf-8"))
        except Exception:
            continue
    return empty_research_agenda()


def format_research_agenda_prompt_block(research_agenda: dict[str, Any] | None) -> str:
    summary = summarize_research_agenda_for_state(research_agenda)
    if not summary:
        return ""

    section_labels = (
        ("themes", "Themes"),
        ("valued_problem_types", "Valued problem types"),
        ("anti_goals", "Anti-goals"),
        ("canonical_targets", "Canonical targets"),
        ("soft_constraints", "Soft constraints"),
    )
    lines = [
        "- Research agenda: treat the following as external value guidance for what kinds of problems are worth generating.",
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
