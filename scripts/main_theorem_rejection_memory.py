from __future__ import annotations

import json
from pathlib import Path
from typing import Any


def load_main_theorem_rejection_memory(memory_path: Path) -> list[dict[str, Any]]:
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
        statement = str(item.get("statement", "")).strip()
        theorem_name_stem = str(item.get("theorem_name_stem", "")).strip()
        verdict = str(item.get("verdict", "")).strip()
        reason = str(item.get("reason", "")).strip()
        if not statement or not theorem_name_stem or not verdict or not reason:
            continue
        safe_rows.append(
            {
                "candidate_id": str(item.get("candidate_id", "")).strip(),
                "statement": statement,
                "theorem_name_stem": theorem_name_stem,
                "rationale": str(item.get("rationale", "")).strip(),
                "verdict": verdict,
                "reason": reason,
                "strongest_objection": str(item.get("strongest_objection", "")).strip(),
                "salvage_plan": str(item.get("salvage_plan", "")).strip(),
                "paper_unit_viability": str(item.get("paper_unit_viability", "")).strip(),
                "novelty": str(item.get("novelty", "")).strip(),
                "significance": str(item.get("significance", "")).strip(),
                "iteration": int(item.get("iteration", 0) or 0),
            }
        )
    return safe_rows


def save_main_theorem_rejection_memory(memory_path: Path, entries: list[dict[str, Any]]) -> None:
    memory_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {"entries": entries[-80:]}
    memory_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def append_main_theorem_rejection_entry(memory_path: Path, entry: dict[str, Any]) -> list[dict[str, Any]]:
    theorem_name_stem = str(entry.get("theorem_name_stem", "")).strip()
    statement = str(entry.get("statement", "")).strip()
    verdict = str(entry.get("verdict", "")).strip()
    reason = str(entry.get("reason", "")).strip()
    if not theorem_name_stem or not statement or not verdict or not reason:
        return load_main_theorem_rejection_memory(memory_path)

    history = load_main_theorem_rejection_memory(memory_path)
    statement_norm = " ".join(statement.lower().split())
    history = [
        row
        for row in history
        if " ".join(str(row.get("statement", "")).lower().split()) != statement_norm
        and str(row.get("candidate_id", "")).strip() != str(entry.get("candidate_id", "")).strip()
    ]
    history.append(
        {
            "candidate_id": str(entry.get("candidate_id", "")).strip(),
            "statement": statement,
            "theorem_name_stem": theorem_name_stem,
            "rationale": str(entry.get("rationale", "")).strip(),
            "verdict": verdict,
            "reason": reason,
            "strongest_objection": str(entry.get("strongest_objection", "")).strip(),
            "salvage_plan": str(entry.get("salvage_plan", "")).strip(),
            "paper_unit_viability": str(entry.get("paper_unit_viability", "")).strip(),
            "novelty": str(entry.get("novelty", "")).strip(),
            "significance": str(entry.get("significance", "")).strip(),
            "iteration": int(entry.get("iteration", 0) or 0),
        }
    )
    save_main_theorem_rejection_memory(memory_path, history)
    return history
