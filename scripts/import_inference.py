from __future__ import annotations


DEFAULT_IMPORTS = ["Mathlib"]


def infer_minimal_imports(
    text: str,
    *,
    probe_kind: str | None = None,
    base_imports: tuple[str, ...] = (),
    repo_root: object | None = None,
) -> list[str]:
    _ = (text, probe_kind, base_imports, repo_root)
    return list(DEFAULT_IMPORTS)


def render_import_block(imports: list[str]) -> str:
    lines: list[str] = []
    for module_name in imports:
        if module_name not in lines:
            lines.append(module_name)
    lines = [f"import {module_name}" for module_name in lines]
    return ("\n".join(lines) + "\n") if lines else ""
