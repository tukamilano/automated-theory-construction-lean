from __future__ import annotations

import json
from pathlib import Path
from typing import Any


def _normalize_string_list(raw: Any, *, max_items: int | None = None) -> list[str]:
    if not isinstance(raw, list):
        return []
    items = [str(item).strip() for item in raw if str(item).strip()]
    if max_items is not None:
        return items[:max_items]
    return items


def load_theorem_reuse_memory(memory_path: Path) -> list[dict[str, Any]]:
    if not memory_path.exists():
        return []
    try:
        payload = json.loads(memory_path.read_text(encoding="utf-8"))
    except Exception:
        return []
    if not isinstance(payload, dict):
        return []

    rows = payload.get("entries", [])
    if not isinstance(rows, list):
        return []

    safe_rows: list[dict[str, Any]] = []
    for item in rows:
        if not isinstance(item, dict):
            continue
        theorem_name = str(item.get("theorem_name", "")).strip()
        statement = str(item.get("statement", "")).strip()
        if not theorem_name or not statement:
            continue
        safe_rows.append(
            {
                "candidate_id": str(item.get("candidate_id", "")).strip(),
                "theorem_name": theorem_name,
                "statement": statement,
                "docstring_summary": str(item.get("docstring_summary", "")).strip(),
                "rationale": str(item.get("rationale", "")).strip(),
                "plan_summary": str(item.get("plan_summary", "")).strip(),
                "supporting_theorems": _normalize_string_list(item.get("supporting_theorems", []), max_items=12),
                "intermediate_lemmas": _normalize_string_list(item.get("intermediate_lemmas", []), max_items=12),
                "iteration": int(item.get("iteration", 0) or 0),
                "appended_to_derived": bool(item.get("appended_to_derived", False)),
            }
        )
    return safe_rows


def save_theorem_reuse_memory(memory_path: Path, entries: list[dict[str, Any]]) -> None:
    memory_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {"entries": entries[-50:]}
    memory_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def append_theorem_reuse_memory_entry(memory_path: Path, entry: dict[str, Any]) -> list[dict[str, Any]]:
    theorem_name = str(entry.get("theorem_name", "")).strip()
    candidate_id = str(entry.get("candidate_id", "")).strip()
    if not theorem_name:
        return load_theorem_reuse_memory(memory_path)

    history = load_theorem_reuse_memory(memory_path)
    history = [
        row for row in history
        if str(row.get("theorem_name", "")).strip() != theorem_name
        and str(row.get("candidate_id", "")).strip() != candidate_id
    ]
    history.append(
        {
            "candidate_id": candidate_id,
            "theorem_name": theorem_name,
            "statement": str(entry.get("statement", "")).strip(),
            "docstring_summary": str(entry.get("docstring_summary", "")).strip(),
            "rationale": str(entry.get("rationale", "")).strip(),
            "plan_summary": str(entry.get("plan_summary", "")).strip(),
            "supporting_theorems": _normalize_string_list(entry.get("supporting_theorems", []), max_items=12),
            "intermediate_lemmas": _normalize_string_list(entry.get("intermediate_lemmas", []), max_items=12),
            "iteration": int(entry.get("iteration", 0) or 0),
            "appended_to_derived": bool(entry.get("appended_to_derived", False)),
        }
    )
    save_theorem_reuse_memory(memory_path, history)
    return history


def summarize_supporting_theorem_frequency(
    entries: list[dict[str, Any]],
    *,
    max_items: int = 20,
) -> list[dict[str, Any]]:
    counts: dict[str, int] = {}
    for entry in entries:
        supporting = entry.get("supporting_theorems", [])
        if not isinstance(supporting, list):
            continue
        for theorem_name in supporting:
            cleaned = str(theorem_name).strip()
            if not cleaned:
                continue
            counts[cleaned] = counts.get(cleaned, 0) + 1

    items = [
        {"theorem_name": theorem_name, "count": count}
        for theorem_name, count in counts.items()
    ]
    items.sort(key=lambda item: (-int(item["count"]), str(item["theorem_name"])))
    return items[:max_items]
