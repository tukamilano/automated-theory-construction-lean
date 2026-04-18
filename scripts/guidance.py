from __future__ import annotations

from typing import Any


def _require_object(value: Any, field_name: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ValueError(f"{field_name} must be an object")
    return dict(value)


def build_guidance_context(
    *,
    theory_state: dict[str, Any] | None,
    research_agenda: dict[str, Any] | None,
    materials: dict[str, Any] | None = None,
) -> dict[str, dict[str, Any]]:
    return {
        "theory_state": dict(theory_state or {}),
        "research_agenda": dict(research_agenda or {}),
        "materials": dict(materials or {}),
    }


def unpack_guidance_context(
    guidance: dict[str, Any] | None,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    payload = dict(guidance or {})
    return (
        _require_object(payload.get("theory_state", {}), "guidance.theory_state"),
        _require_object(payload.get("research_agenda", {}), "guidance.research_agenda"),
        _require_object(payload.get("materials", {}), "guidance.materials"),
    )
