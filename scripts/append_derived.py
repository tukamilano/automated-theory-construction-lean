from __future__ import annotations

import argparse
import re
from pathlib import Path

from import_inference import infer_minimal_imports, render_import_block


THEOREM_NAME_PATTERN = re.compile(r"\btheorem\s+([A-Za-z0-9_']+)\b")
THEOREM_HEADER_PATTERN = re.compile(r"\btheorem\s+([A-Za-z0-9_']+)\s*:\s*(.+?)\s*:=", re.DOTALL)
LEAN_DECL_NAME_PATTERN = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
LEAN_IMPORT_PATTERN = re.compile(r"^import\s+([A-Za-z0-9_.']+)\s*$", re.MULTILINE)


def normalize_statement_text(statement: str) -> str:
    return " ".join(statement.split())


def build_derived_entry(theorem_name: str, statement: str) -> dict[str, str]:
    return {
        "theorem_name": theorem_name.strip(),
        "statement": normalize_statement_text(statement),
    }


def validate_theorem_name(theorem_name: str) -> str:
    cleaned = theorem_name.strip()
    if not cleaned:
        raise ValueError("theorem_name must be non-empty")
    if cleaned == "None":
        raise ValueError("theorem_name must not be the literal None")
    if not LEAN_DECL_NAME_PATTERN.fullmatch(cleaned):
        raise ValueError("theorem_name must match ^[A-Za-z_][A-Za-z0-9_']*$")
    return cleaned


def iter_theorem_headers(derived_file: Path, max_theorems: int | None = None) -> list[tuple[str, str]]:
    if not derived_file.exists():
        return []
    try:
        content = derived_file.read_text(encoding="utf-8")
    except Exception:
        return []

    entries: list[tuple[str, str]] = []
    for line in content.splitlines():
        match = THEOREM_HEADER_PATTERN.search(line)
        if not match:
            continue
        theorem_name = match.group(1).strip()
        statement = normalize_statement_text(match.group(2))
        if not theorem_name or not statement:
            continue
        entries.append((theorem_name, statement))
        if max_theorems is not None and len(entries) >= max_theorems:
            break
    return entries


def build_derived_entries_from_file(derived_file: Path, max_theorems: int | None = None) -> list[dict[str, str]]:
    theorem_rows = iter_theorem_headers(derived_file, max_theorems=max_theorems)
    return [build_derived_entry(theorem_name, statement) for theorem_name, statement in theorem_rows]


def ensure_imports(content: str, required_imports: list[str]) -> str:
    if not required_imports:
        return content

    existing_imports = {match.group(1) for match in LEAN_IMPORT_PATTERN.finditer(content)}
    missing_imports = [module_name for module_name in required_imports if module_name not in existing_imports]
    if not missing_imports:
        return content

    namespace_match = re.search(r"^namespace\s+AutomatedTheoryConstruction\s*$", content, re.MULTILINE)
    if namespace_match is None:
        raise ValueError("Derived file is missing namespace marker")

    prefix = content[: namespace_match.start()]
    if prefix and not prefix.endswith("\n"):
        prefix += "\n"
    if prefix and not prefix.endswith("\n\n"):
        prefix += "\n"
    return prefix + render_import_block(missing_imports) + content[namespace_match.start() :]


def append_theorem(
    derived_file: Path,
    theorem_code: str,
    theorem_name: str | None = None,
) -> bool:
    derived_file.parent.mkdir(parents=True, exist_ok=True)
    required_imports = infer_minimal_imports(theorem_code)
    if not derived_file.exists():
        derived_file.write_text(
            render_import_block(required_imports)
            + "import AutomatedTheoryConstruction.Theory\n\nnamespace AutomatedTheoryConstruction\n\nend AutomatedTheoryConstruction\n",
            encoding="utf-8",
        )

    if theorem_name is None:
        match = THEOREM_NAME_PATTERN.search(theorem_code)
        if not match:
            raise ValueError("Could not detect theorem name from theorem_code")
        theorem_name = match.group(1)
    theorem_name = validate_theorem_name(theorem_name)

    content = derived_file.read_text(encoding="utf-8")
    content = ensure_imports(content, required_imports)
    blocks_to_add: list[str] = []

    if not re.search(rf"\btheorem\s+{re.escape(theorem_name)}\b", content):
        blocks_to_add.append(theorem_code.strip())
    if not blocks_to_add:
        return False

    end_marker = "end AutomatedTheoryConstruction"
    idx = content.rfind(end_marker)
    if idx == -1:
        raise ValueError("Derived file is missing end namespace marker")

    insert = "\n" + "\n\n".join(blocks_to_add) + "\n\n"
    new_content = content[:idx] + insert + content[idx:]
    derived_file.write_text(new_content, encoding="utf-8")
    return True


def main() -> None:
    parser = argparse.ArgumentParser(description="Append a verified theorem to Derived.lean")
    parser.add_argument("--derived-file", default="AutomatedTheoryConstruction/Derived.lean")
    parser.add_argument("--theorem-name")
    parser.add_argument("--theorem-code-file")
    args = parser.parse_args()

    derived_file = Path(args.derived_file)
    if not args.theorem_code_file:
        raise ValueError("--theorem-code-file is required")
    theorem_code = Path(args.theorem_code_file).read_text(encoding="utf-8")
    appended = append_theorem(derived_file, theorem_code, args.theorem_name)
    print({"appended": appended})


if __name__ == "__main__":
    main()
