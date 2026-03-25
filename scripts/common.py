from __future__ import annotations

import json
import os
import re
import tempfile
from pathlib import Path
from typing import Any


ID_PATTERN = re.compile(r"^op_(\d+)$")
OPEN_PROBLEM_PRIORITY_LABELS = {"high", "medium", "low", "unknown"}
ARCHIVED_PROBLEMS_FILENAME = "archived_problems.jsonl"
LEGACY_DEFERRED_PROBLEMS_FILENAME = "deferred_problems.jsonl"
LEGACY_PRUNED_OPEN_PROBLEMS_FILENAME = "pruned_open_problems.jsonl"


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
    normalized["failure_count"] = _coerce_nonnegative_int(normalized.get("failure_count"), 0)
    normalized.pop("priority_refreshed_at_theorem_count", None)
    normalized.pop("attempt_count", None)
    normalized.pop("last_attempt_iteration", None)
    normalized.pop("last_result", None)
    normalized.pop("pruned_at_iteration", None)
    normalized.pop("pruned_reason", None)
    return normalized


def dedupe_problem_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    deduped: list[dict[str, Any]] = []
    seen_ids: set[str] = set()
    for row in rows:
        normalized = normalize_open_problem_row(row)
        problem_id = str(normalized.get("id", "")).strip()
        if not problem_id or problem_id in seen_ids:
            continue
        seen_ids.add(problem_id)
        deduped.append(normalized)
    return deduped


def read_archived_problem_rows(data_dir: Path) -> list[dict[str, Any]]:
    paths = [
        data_dir / ARCHIVED_PROBLEMS_FILENAME,
        data_dir / LEGACY_DEFERRED_PROBLEMS_FILENAME,
        data_dir / LEGACY_PRUNED_OPEN_PROBLEMS_FILENAME,
    ]
    combined_rows: list[dict[str, Any]] = []
    for path in paths:
        combined_rows.extend(read_jsonl(path))
    return dedupe_problem_rows(combined_rows)


def is_active_open_problem(row: dict[str, Any], *, failure_threshold: int) -> bool:
    normalized = normalize_open_problem_row(row)
    if normalize_open_problem_priority(normalized.get("priority")) == "low":
        return False
    failure_count = int(normalized.get("failure_count", 0) or 0)
    if failure_threshold > 0 and failure_count >= failure_threshold:
        return False
    return True


def partition_open_problem_rows(
    rows: list[dict[str, Any]],
    *,
    failure_threshold: int,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    active_rows: list[dict[str, Any]] = []
    archived_rows: list[dict[str, Any]] = []
    for row in rows:
        normalized = normalize_open_problem_row(row)
        if is_active_open_problem(normalized, failure_threshold=failure_threshold):
            active_rows.append(normalized)
        else:
            archived_rows.append(normalized)
    return active_rows, archived_rows
