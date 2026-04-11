from __future__ import annotations

from pathlib import Path

from generated_library import build_library_entries


def extract_derived_theorem_entries(
    derived_path: Path,
    max_theorems: int | None = None,
) -> list[dict[str, str]]:
    """Extract theorem entries from Generated plus the active Derived frontier."""
    generated_root = derived_path.parent / "Generated"
    fallback_entries = build_library_entries(generated_root=generated_root, derived_file=derived_path)
    return [
        {
            "name": str(entry.get("theorem_name", "")).strip(),
            "statement": str(entry.get("statement", "")).strip(),
        }
        for entry in fallback_entries[:max_theorems]
        if str(entry.get("theorem_name", "")).strip() and str(entry.get("statement", "")).strip()
    ]
