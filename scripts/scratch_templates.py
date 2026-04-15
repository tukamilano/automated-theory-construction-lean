from __future__ import annotations

from pathlib import Path


DEFAULT_REPO_ROOT = Path(__file__).resolve().parent.parent


def _module_file_for(module_name: str, *, repo_root: Path) -> Path:
    return repo_root / (module_name.replace(".", "/") + ".lean")


def module_exists(module_name: str, *, repo_root: Path = DEFAULT_REPO_ROOT) -> bool:
    return _module_file_for(module_name, repo_root=repo_root).exists()


def scratch_import_modules(*, repo_root: Path = DEFAULT_REPO_ROOT) -> list[str]:
    modules = ["Mathlib"]
    for module_name in (
        "AutomatedTheoryConstruction.Lambek",
        "AutomatedTheoryConstruction.Derived",
    ):
        if module_exists(module_name, repo_root=repo_root):
            modules.append(module_name)
    return modules


def render_scratch_template(*, repo_root: Path = DEFAULT_REPO_ROOT) -> str:
    import_block = "\n".join(
        f"import {module_name}"
        for module_name in scratch_import_modules(repo_root=repo_root)
    )
    return (
        import_block
        + "\n\n"
        + "set_option autoImplicit false\n\n"
        + "namespace AutomatedTheoryConstruction\n\n"
        + "-- Temporary Lean code for verification is written here.\n\n"
        + "end AutomatedTheoryConstruction\n"
    )
