from __future__ import annotations

import re


IMPORT_RULES: tuple[tuple[re.Pattern[str], str], ...] = (
    (re.compile(r"\bNat\.iterate\b|\^\["), "Mathlib.Logic.Function.Iterate"),
)


def infer_minimal_imports(text: str) -> list[str]:
    imports: list[str] = []
    for pattern, module_name in IMPORT_RULES:
        if pattern.search(text) and module_name not in imports:
            imports.append(module_name)
    return imports


def render_import_block(imports: list[str]) -> str:
    lines = [f"import {module_name}" for module_name in imports]
    return ("\n".join(lines) + "\n") if lines else ""
