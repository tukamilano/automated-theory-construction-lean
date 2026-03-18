from __future__ import annotations

import json
import os
import re
import tempfile
from pathlib import Path
from typing import Any


ID_PATTERN = re.compile(r"^op_(\d+)$")


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


def load_defaults(config_path: Path) -> dict[str, Any]:
    if not config_path.exists():
        return {}
    return json.loads(config_path.read_text(encoding="utf-8"))


def resolve_max_attempts(cli_value: int | None, config_path: Path) -> int:
    if cli_value is not None:
        return cli_value
    env_value = os.getenv("ATC_MAX_ATTEMPTS")
    if env_value is not None and env_value.strip().isdigit():
        return max(1, int(env_value.strip()))
    defaults = load_defaults(config_path)
    from_config = defaults.get("max_attempts")
    if isinstance(from_config, int) and from_config > 0:
        return from_config
    return 5
