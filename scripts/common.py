from __future__ import annotations

import json
import os
import re
import tempfile
from pathlib import Path
from typing import Any


ID_PATTERN = re.compile(r"^op_(\d+)$")
OPEN_PROBLEM_PRIORITY_LABELS = {"high", "medium", "low", "unknown"}


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        rows.append(json.loads(line))
    return rows


def write_jsonl_atomic(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = "".join(json.dumps(row, ensure_ascii=False, separators=(",", ":")) + "\n" for row in rows)
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=str(path.parent), delete=False) as tmp:
        tmp.write(payload)
        tmp_path = Path(tmp.name)
    os.replace(tmp_path, path)


def normalize_stmt(stmt: str) -> str:
    return " ".join(stmt.strip().lower().split())


def parse_problem_index(problem_id: str) -> int | None:
    match = ID_PATTERN.match(problem_id)
    if not match:
        return None
    return int(match.group(1))


def next_problem_id(all_ids: list[str]) -> str:
    max_index = 0
    for problem_id in all_ids:
        idx = parse_problem_index(problem_id)
        if idx is not None and idx > max_index:
            max_index = idx
    return f"op_{max_index + 1:06d}"


def _coerce_nonnegative_int(value: Any, default: int) -> int:
    try:
        parsed = int(value)
    except (TypeError, ValueError):
        return default
    return parsed if parsed >= 0 else default


def normalize_open_problem_priority(value: Any) -> str:
    raw = str(value or "").strip().lower()
    if raw in OPEN_PROBLEM_PRIORITY_LABELS:
        return raw
    try:
        parsed = int(raw)
    except (TypeError, ValueError):
        return "unknown"
    if parsed >= 3:
        return "high"
    if parsed == 2:
        return "medium"
    if parsed == 1:
        return "low"
    return "unknown"


def normalize_open_problem_row(row: dict[str, Any]) -> dict[str, Any]:
    normalized = dict(row)
    normalized.pop("n", None)

    src = str(normalized.get("src", "generated") or "generated").strip() or "generated"
    normalized["src"] = src
    normalized["priority"] = normalize_open_problem_priority(normalized.get("priority"))
    normalized["priority_rationale"] = str(normalized.get("priority_rationale", "") or "").strip()
    normalized["priority_refreshed_at_theorem_count"] = _coerce_nonnegative_int(
        normalized.get("priority_refreshed_at_theorem_count"),
        0,
    )
    normalized["attempt_count"] = _coerce_nonnegative_int(normalized.get("attempt_count"), 0)
    normalized["failure_count"] = _coerce_nonnegative_int(normalized.get("failure_count"), 0)
    normalized["last_attempt_iteration"] = _coerce_nonnegative_int(
        normalized.get("last_attempt_iteration"),
        0,
    )
    normalized["last_result"] = str(normalized.get("last_result", "") or "").strip()
    return normalized
