from __future__ import annotations

import re
from pathlib import Path


INCLUDE_PATTERN = re.compile(r"^\s*<!--\s*INCLUDE:\s*(.+?)\s*-->\s*$")


def load_prompt_file(path: Path) -> str:
    return _load_prompt_file(path.resolve(), seen=[])


def _load_prompt_file(path: Path, *, seen: list[Path]) -> str:
    if path in seen:
        cycle = " -> ".join(str(item) for item in [*seen, path])
        raise ValueError(f"Prompt include cycle detected: {cycle}")
    if not path.exists():
        raise ValueError(f"Prompt file not found: {path}")

    lines: list[str] = []
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        match = INCLUDE_PATTERN.match(raw_line)
        if not match:
            lines.append(raw_line)
            continue
        include_path = (path.parent / match.group(1).strip()).resolve()
        lines.append(_load_prompt_file(include_path, seen=[*seen, path]))
    return "\n".join(lines) + "\n"
