from __future__ import annotations

import argparse
import re
from pathlib import Path


THEOREM_NAME_PATTERN = re.compile(r"\btheorem\s+([A-Za-z0-9_']+)\b")


def append_theorem(derived_file: Path, theorem_code: str, theorem_name: str | None = None) -> bool:
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
    if re.search(rf"\btheorem\s+{re.escape(theorem_name)}\b", content):
        return False

    end_marker = "end AutomatedTheoryConstruction"
    idx = content.rfind(end_marker)
    if idx == -1:
        raise ValueError("Derived file is missing end namespace marker")

    insert = "\n" + theorem_code.strip() + "\n\n"
    new_content = content[:idx] + insert + content[idx:]
    derived_file.write_text(new_content, encoding="utf-8")
    return True


def main() -> None:
    parser = argparse.ArgumentParser(description="Append a verified theorem to Derived.lean")
    parser.add_argument("--derived-file", default="AutomatedTheoryConstruction/Derived.lean")
    parser.add_argument("--theorem-name")
    parser.add_argument("--theorem-code-file", required=True)
    args = parser.parse_args()

    theorem_code = Path(args.theorem_code_file).read_text(encoding="utf-8")
    appended = append_theorem(Path(args.derived_file), theorem_code, args.theorem_name)
    print({"appended": appended})


if __name__ == "__main__":
    main()
