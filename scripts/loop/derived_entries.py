from __future__ import annotations

from pathlib import Path

from append_derived import build_derived_entries_from_file
from theorem_store import product_file_for_derived


def extract_derived_theorem_entries(
    derived_path: Path,
    max_theorems: int | None = None,
) -> list[dict[str, str]]:
    """Extract theorem entries from Product plus the active Derived staging file."""
    merged_entries: list[dict[str, str]] = []
    seen: set[tuple[str, str]] = set()
    for source_file in (product_file_for_derived(derived_path), derived_path):
        for entry in build_derived_entries_from_file(source_file):
            name = str(entry.get("theorem_name", "")).strip()
            statement = str(entry.get("statement", "")).strip()
            if not name or not statement:
                continue
            key = (name, statement)
            if key in seen:
                continue
            seen.add(key)
            merged_entries.append({"name": name, "statement": statement})
            if max_theorems is not None and len(merged_entries) >= max_theorems:
                return merged_entries
    return merged_entries
