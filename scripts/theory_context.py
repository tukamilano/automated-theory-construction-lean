from __future__ import annotations

from pathlib import Path


def theory_package_dir(theory_file: Path) -> Path:
    return theory_file.with_suffix("")


def collect_theory_context_files(theory_file: Path) -> list[Path]:
    resolved_entry = theory_file.resolve()
    if not resolved_entry.exists():
        raise ValueError(f"Theory file not found: {resolved_entry}")
    files = [resolved_entry]
    package_dir = theory_package_dir(resolved_entry)
    if not package_dir.is_dir():
        return files

    package_files = sorted(
        path.resolve()
        for path in package_dir.rglob("*.lean")
        if path.is_file()
    )
    files.extend(package_files)
    return files


def load_theory_context_bundle(theory_file: Path) -> str:
    chunks: list[str] = []
    for path in collect_theory_context_files(theory_file):
        body = path.read_text(encoding="utf-8").rstrip()
        chunks.append(
            f"-- BEGIN THEORY FILE: {path}\n"
            f"{body}\n"
            f"-- END THEORY FILE: {path}"
        )
    return "\n\n".join(chunks)


def load_optional_theory_context_bundle(theory_file: Path) -> str:
    if not theory_file.exists():
        return ""
    return load_theory_context_bundle(theory_file)
