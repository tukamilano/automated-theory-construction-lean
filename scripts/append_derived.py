from __future__ import annotations

import argparse
import re
from pathlib import Path


THEOREM_NAME_PATTERN = re.compile(r"\btheorem\s+([A-Za-z0-9_']+)\b")
THEOREM_HEADER_PATTERN = re.compile(r"\btheorem\s+([A-Za-z0-9_']+)\s*:\s*(.+?)\s*:=", re.DOTALL)
PROBLEM_THEOREM_PATTERN = re.compile(r"^thm_(op_\d{6})(?:_is_false)?$")

SEMIGROUP_PREFIX = "∀ {α : Type u} [SemigroupLike01 α], "

COMMON_STATEMENT_ALIASES = {
    "∀ x y z : α, (x * y) * z = x * (y * z)": "mul_assoc",
    "∀ x y : α, x * y = y * x": "mul_comm",
    "∀ x : α, x * x = x": "mul_idem",
    "∀ x y z : α, x * y = x * z → y = z": "mul_left_cancel",
    "∀ join : α → α → α, ∀ x y z : α, x * (join y z) = join (x * y) (x * z)": "left_distrib_join",
    "∀ x y z : α, (x * y) * (x * z) = (x * y) * z": "mul_right_absorb_after_left_factor",
    "∀ x y z : α, x * (y * z) = (x * y) * (x * z)": "left_expand_nested_mul",
    "∀ x y : α, (x * y) * x = x * y": "mul_right_absorb_lhs",
    "∀ x y : α, (x * y) * y = x * y": "mul_right_absorb_rhs",
    "∀ meet : α → α → α, ∀ x y : α, x * (meet x y) = x": "left_absorb_meet",
    "∃ e : α, ∀ x : α, e * x = x ∧ x * e = x": "exists_two_sided_identity",
    "∃ e : α, ∀ x : α, ∃ y : α, x * y = e ∧ y * x = e": "exists_two_sided_sink",
    "{e : α}, (∀ x : α, e * x = x) → ∀ x : α, x * e = x": "left_identity_implies_right_identity",
    "{e : α}, (∀ x : α, e * x = x) → ∀ x y : α, x * y = y * x": "left_identity_implies_mul_comm",
}


def normalize_statement_text(statement: str) -> str:
    return " ".join(statement.split())


def unwrap_outer_negation(statement: str) -> tuple[bool, str]:
    text = normalize_statement_text(statement)
    if text.startswith("¬(") and text.endswith(")"):
        return True, text[2:-1].strip()
    return False, text


def drop_standard_context_prefix(statement: str) -> str:
    text = normalize_statement_text(statement)
    if text.startswith(SEMIGROUP_PREFIX):
        return text[len(SEMIGROUP_PREFIX) :].strip()
    return text


def slugify_statement(statement: str) -> str:
    text = drop_standard_context_prefix(statement)
    replacements = {
        "∀": " forall ",
        "∃": " exists ",
        "→": " implies ",
        "∧": " and ",
        "∨": " or ",
        "¬": " not ",
        "≠": " ne ",
        "=": " eq ",
        "*": " mul ",
        ":": " ",
        ",": " ",
        "(": " ",
        ")": " ",
        "{": " ",
        "}": " ",
        "[": " ",
        "]": " ",
        "α": " alpha ",
    }
    for old, new in replacements.items():
        text = text.replace(old, new)

    raw_tokens = re.findall(r"[A-Za-z0-9_']+", text)
    stopwords = {
        "forall",
        "exists",
        "Type",
        "u",
        "alpha",
        "SemigroupLike01",
        "x",
        "y",
        "z",
    }

    tokens: list[str] = []
    seen: set[str] = set()
    for token in raw_tokens:
        if token in stopwords:
            continue
        if token in seen:
            continue
        seen.add(token)
        tokens.append(token.lower())
        if len(tokens) >= 6:
            break

    if not tokens:
        return "derived_fact"
    return "_".join(tokens)


def infer_alias_core(statement: str) -> str:
    is_negated, inner = unwrap_outer_negation(statement)
    normalized_inner = drop_standard_context_prefix(inner)
    core = COMMON_STATEMENT_ALIASES.get(normalized_inner, slugify_statement(inner))
    if is_negated and not core.startswith("not_"):
        core = f"not_{core}"
    return core


def infer_alias_name(theorem_name: str, statement: str) -> str | None:
    match = PROBLEM_THEOREM_PATTERN.match(theorem_name)
    if not match:
        return None

    alias_core = infer_alias_core(statement)
    alias_name = re.sub(r"[^A-Za-z0-9_']+", "_", f"{alias_core}_{match.group(1)}").strip("_")
    alias_name = re.sub(r"_+", "_", alias_name)
    if not alias_name or alias_name == theorem_name:
        return None
    if alias_name[0].isdigit():
        alias_name = f"derived_{alias_name}"
    return alias_name


def is_canonical_problem_theorem(name: str) -> bool:
    return bool(re.fullmatch(r"thm_op_\d{6}(?:_is_false)?", name))


def name_priority(name: str) -> tuple[int, int, str]:
    return (
        1 if is_canonical_problem_theorem(name) else 0,
        len(name),
        name,
    )


def choose_preferred_theorem_name(names: list[str]) -> str:
    cleaned = [name.strip() for name in names if name.strip()]
    if not cleaned:
        raise ValueError("expected at least one theorem name")
    return sorted(dict.fromkeys(cleaned), key=name_priority)[0]


def build_derived_entry(
    theorem_name: str,
    statement: str,
    alias_names: list[str] | None = None,
) -> dict[str, list[str] | str]:
    names = [theorem_name]
    if alias_names:
        names.extend(alias_names)
    ordered_names = sorted(dict.fromkeys(name.strip() for name in names if name.strip()), key=name_priority)
    preferred_name = ordered_names[0]
    return {
        "theorem_name": preferred_name,
        "statement": normalize_statement_text(statement),
        "alias_names": [name for name in ordered_names if name != preferred_name],
    }


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


def build_derived_entries_from_file(derived_file: Path, max_theorems: int | None = None) -> list[dict[str, list[str] | str]]:
    theorem_rows = iter_theorem_headers(derived_file, max_theorems=max_theorems)
    grouped_names: dict[str, list[str]] = {}
    ordered_statements: list[str] = []
    statement_texts: dict[str, str] = {}

    for theorem_name, statement in theorem_rows:
        statement_key = normalize_statement_text(statement)
        if statement_key not in grouped_names:
            grouped_names[statement_key] = []
            ordered_statements.append(statement_key)
            statement_texts[statement_key] = statement
        grouped_names[statement_key].append(theorem_name)

    entries: list[dict[str, Any]] = []
    for statement_key in ordered_statements:
        names = sorted(dict.fromkeys(grouped_names[statement_key]), key=name_priority)
        preferred_name = choose_preferred_theorem_name(names)
        alias_names = [name for name in names if name != preferred_name]
        entries.append(build_derived_entry(preferred_name, statement_texts[statement_key], alias_names))
    return entries


def build_alias_theorem(theorem_code: str, theorem_name: str | None = None) -> tuple[str | None, str | None]:
    match = THEOREM_HEADER_PATTERN.search(theorem_code)
    if not match:
        return None, None

    parsed_name = match.group(1)
    statement = normalize_statement_text(match.group(2))
    canonical_name = theorem_name or parsed_name
    alias_name = infer_alias_name(canonical_name, statement)
    if alias_name is None:
        return None, None

    alias_code = f"theorem {alias_name} : {statement} := {parsed_name}"
    return alias_name, alias_code


def append_theorem(
    derived_file: Path,
    theorem_code: str,
    theorem_name: str | None = None,
) -> bool:
    derived_file.parent.mkdir(parents=True, exist_ok=True)
    if not derived_file.exists():
        derived_file.write_text(
            "import AutomatedTheoryConstruction.Theory\n\nnamespace AutomatedTheoryConstruction\n\nend AutomatedTheoryConstruction\n",
            encoding="utf-8",
        )

    if theorem_name is None:
        match = THEOREM_NAME_PATTERN.search(theorem_code)
        if not match:
            raise ValueError("Could not detect theorem name from theorem_code")
        theorem_name = match.group(1)

    content = derived_file.read_text(encoding="utf-8")
    alias_name, alias_code = build_alias_theorem(theorem_code, theorem_name)
    blocks_to_add: list[str] = []

    if not re.search(rf"\btheorem\s+{re.escape(theorem_name)}\b", content):
        blocks_to_add.append(theorem_code.strip())
    if alias_name and alias_code and not re.search(rf"\btheorem\s+{re.escape(alias_name)}\b", content):
        blocks_to_add.append(alias_code)
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
