from __future__ import annotations

import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "loop"))


from loop_helpers import extract_derived_entry_from_theorem_code


def main() -> int:
    theorem_code = """
/-- Ordinary support closure captures exactly the coarse admissibility predicate `support_ok`. -/
theorem support_closure_iff_support_ok
    (Γ : List Tp) (A : Tp) :
    SupportClosure Γ A ↔ support_ok Γ A := by
  simpa using thm_support_closure_matches_support_ok_000036 Γ A
""".strip()
    entry = extract_derived_entry_from_theorem_code(theorem_code)
    if entry is None:
        raise RuntimeError("expected theorem entry for binder-style theorem")
    if entry.get("name") != "support_closure_iff_support_ok":
        raise RuntimeError(f"unexpected theorem name: {entry}")
    statement = str(entry.get("statement", ""))
    if "(Γ : List Tp) (A : Tp)" not in statement:
        raise RuntimeError(f"expected binders in extracted statement: {entry}")
    if "SupportClosure Γ A ↔ support_ok Γ A" not in statement:
        raise RuntimeError(f"expected proposition in extracted statement: {entry}")
    print("theorem entry extraction test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
