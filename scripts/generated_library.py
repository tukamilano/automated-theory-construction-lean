from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from append_derived import build_derived_entries_from_file
from common import write_json_atomic


DEFAULT_GENERATED_ROOT = Path("AutomatedTheoryConstruction/Generated")
DEFAULT_GENERATED_MANIFEST = DEFAULT_GENERATED_ROOT / "Manifest.lean"
DEFAULT_GENERATED_CATALOG = DEFAULT_GENERATED_ROOT / "catalog.json"

_BASE_IMPORTS = (
    "import Mathlib\n"
    "import AutomatedTheoryConstruction.Theory\n"
)

_COMMON_PREAMBLE = (
    "set_option autoImplicit false\n\n"
    "namespace AutomatedTheoryConstruction\n\n"
    "open Mathling.Lambek.ProductFree\n"
    "open scoped Mathling.Lambek.ProductFree\n\n"
)
CHUNK_STEM_PATTERN = re.compile(r"^C(\d{4})(?:_|$)")


def render_scratch_template(*, include_generated_manifest: bool = True) -> str:
    imports = [
        "import Mathlib",
        "import AutomatedTheoryConstruction.Lambek",
    ]
    if include_generated_manifest:
        imports.append("import AutomatedTheoryConstruction.Generated.Manifest")
    imports.append("import AutomatedTheoryConstruction.Derived")
    import_block = "\n".join(imports)
    return (
        import_block
        + "\n\n"
        + "set_option autoImplicit false\n\n"
        + "namespace AutomatedTheoryConstruction\n\n"
        + "open Mathling.Lambek.ProductFree\n"
        + "open scoped Mathling.Lambek.ProductFree\n\n"
        + "-- Temporary Lean code generated for verification is written here.\n\n"
        + "end AutomatedTheoryConstruction\n"
    )


def _render_manifest(import_modules: list[str]) -> str:
    import_lines = [f"import {module_name}" for module_name in import_modules]
    body = "\n".join(import_lines).strip()
    return (body + "\n") if body else "-- Generated manifest\n"


def ensure_generated_scaffold(
    *,
    generated_root: Path,
    manifest_file: Path,
    catalog_file: Path,
) -> None:
    generated_root.mkdir(parents=True, exist_ok=True)
    if not manifest_file.exists():
        manifest_file.write_text(_render_manifest([]), encoding="utf-8")
    if not catalog_file.exists():
        write_json_atomic(catalog_file, {"version": 1, "chunks": []})


def iter_generated_chunk_files(generated_root: Path) -> list[Path]:
    if not generated_root.exists():
        return []

    def sort_key(path: Path) -> tuple[int, str]:
        match = CHUNK_STEM_PATTERN.search(path.stem)
        if match:
            return int(match.group(1)), path.name
        return 10**9, path.name

    return sorted(
        (path for path in generated_root.glob("*.lean") if path.name != "Manifest.lean"),
        key=sort_key,
    )


def build_library_entries(*, generated_root: Path, derived_file: Path) -> list[dict[str, str]]:
    entries: list[dict[str, str]] = []
    for chunk_file in iter_generated_chunk_files(generated_root):
        entries.extend(build_derived_entries_from_file(chunk_file))
    entries.extend(build_derived_entries_from_file(derived_file))
    return entries


def render_generated_chunk(
    *,
    prior_module: str | None,
    body: str,
) -> str:
    imports = [_BASE_IMPORTS.rstrip()]
    if prior_module:
        imports.append(f"import {prior_module}")
    import_block = "\n".join(imports).strip() + "\n\n"
    cleaned_body = body.strip()
    if cleaned_body:
        cleaned_body += "\n\n"
    return import_block + _COMMON_PREAMBLE + cleaned_body + "end AutomatedTheoryConstruction\n"


def write_generated_catalog(catalog_file: Path, *, chunks: list[dict[str, Any]]) -> None:
    write_json_atomic(catalog_file, {"version": 1, "chunks": chunks})


def write_generated_manifest(manifest_file: Path, *, import_modules: list[str]) -> None:
    manifest_file.write_text(_render_manifest(import_modules), encoding="utf-8")
