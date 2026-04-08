from __future__ import annotations

from typing import Any


def build_guidance_context(
    *,
    theory_state: dict[str, Any] | None,
    research_agenda: dict[str, Any] | None,
) -> dict[str, dict[str, Any]]:
    return {
        "theory_state": dict(theory_state or {}),
        "research_agenda": dict(research_agenda or {}),
    }


def unpack_guidance_context(
    guidance: dict[str, Any] | None,
) -> tuple[dict[str, Any], dict[str, Any]]:
    payload = dict(guidance or {})
    theory_state = payload.get("theory_state")
    research_agenda = payload.get("research_agenda")
    if not isinstance(theory_state, dict):
        raise ValueError("guidance.theory_state must be an object")
    if not isinstance(research_agenda, dict):
        raise ValueError("guidance.research_agenda must be an object")
    return dict(theory_state), dict(research_agenda)
