from __future__ import annotations

import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))


from append_derived import append_theorem


def main() -> int:
    theorem_code = """
universe u

inductive TmpBox (α : Type u) where
  | mk : α -> TmpBox α

def tmpId {α : Type u} (x : α) : α := x

theorem thm_tmp_box_id : tmpId 1 = 1 := by
  rfl
""".strip()

    with tempfile.TemporaryDirectory() as tmpdir:
        derived_path = Path(tmpdir) / "Derived.lean"
        derived_path.write_text(
            "import Mathlib\n"
            "import AutomatedTheoryConstruction.Theory\n\n"
            "namespace AutomatedTheoryConstruction\n\n"
            "end AutomatedTheoryConstruction\n",
            encoding="utf-8",
        )
        appended = append_theorem(
            derived_path,
            theorem_code,
            "thm_tmp_box_id",
            "temporary theorem docstring",
        )
        if not appended:
            raise RuntimeError("append_theorem unexpectedly returned False")

        content = derived_path.read_text(encoding="utf-8")
        if "/-- temporary theorem docstring -/\nuniverse u" in content:
            raise RuntimeError("docstring was incorrectly attached to prelude before universe declaration")
        expected_fragment = "/-- temporary theorem docstring -/\ntheorem thm_tmp_box_id"
        if expected_fragment not in content:
            raise RuntimeError("docstring was not placed immediately before theorem declaration")

        duplicate_prelude_theorem = """
open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

theorem thm_tmp_dup : True := by
  trivial
""".strip()
        derived_path.write_text(
            "import Mathlib\n"
            "import AutomatedTheoryConstruction.Theory\n\n"
            "namespace AutomatedTheoryConstruction\n\n"
            "open Mathling.Lambek.ProductFree\n"
            "open scoped Mathling.Lambek.ProductFree\n\n"
            "end AutomatedTheoryConstruction\n",
            encoding="utf-8",
        )
        appended_dup = append_theorem(
            derived_path,
            duplicate_prelude_theorem,
            "thm_tmp_dup",
            "",
        )
        if not appended_dup:
            raise RuntimeError("append_theorem unexpectedly returned False for duplicate prelude case")
        dup_content = derived_path.read_text(encoding="utf-8")
        if dup_content.count("open Mathling.Lambek.ProductFree") != 1:
            raise RuntimeError("duplicate prelude open was appended to Derived")
        if dup_content.count("open scoped Mathling.Lambek.ProductFree") != 1:
            raise RuntimeError("duplicate scoped prelude open was appended to Derived")

    print("append derived prelude test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
