from __future__ import annotations

import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "loop"))


import run_loop
from paper_claim import paper_claim_session


def main() -> int:
    expected_import = "import AutomatedTheoryConstruction.Derived"
    expected_product_import = "import AutomatedTheoryConstruction.Product"
    tracked_scratch = REPO_ROOT / "AutomatedTheoryConstruction" / "Scratch.lean"
    tracked_derived = REPO_ROOT / "AutomatedTheoryConstruction" / "Derived.lean"
    tracked_product = REPO_ROOT / "AutomatedTheoryConstruction" / "Product.lean"
    if expected_import not in tracked_scratch.read_text(encoding="utf-8"):
        raise RuntimeError("tracked Scratch.lean is missing Derived import")
    if expected_product_import not in tracked_derived.read_text(encoding="utf-8"):
        raise RuntimeError("tracked Derived.lean is missing Product import")
    if expected_import in tracked_derived.read_text(encoding="utf-8"):
        raise RuntimeError("tracked Derived.lean should not import itself")
    if expected_product_import in tracked_product.read_text(encoding="utf-8"):
        raise RuntimeError("tracked Product.lean should not import itself")
    if expected_import not in run_loop.SCRATCH_TEMPLATE:
        raise RuntimeError("run_loop SCRATCH_TEMPLATE is missing Derived import")
    if expected_product_import not in run_loop.DERIVED_TEMPLATE:
        raise RuntimeError("run_loop DERIVED_TEMPLATE is missing Product import")
    if expected_import in run_loop.DERIVED_TEMPLATE:
        raise RuntimeError("run_loop DERIVED_TEMPLATE should not import Derived")
    if expected_import not in paper_claim_session.SCRATCH_TEMPLATE:
        raise RuntimeError("paper_claim_session SCRATCH_TEMPLATE is missing Derived import")
    unexpected_open = "open Mathling.Lambek.ProductFree"
    unexpected_open_scoped = "open scoped Mathling.Lambek.ProductFree"
    for label, text in (
        ("tracked Scratch.lean", tracked_scratch.read_text(encoding="utf-8")),
        ("tracked Derived.lean", tracked_derived.read_text(encoding="utf-8")),
        ("tracked Product.lean", tracked_product.read_text(encoding="utf-8")),
        ("run_loop SCRATCH_TEMPLATE", run_loop.SCRATCH_TEMPLATE),
        ("run_loop DERIVED_TEMPLATE", run_loop.DERIVED_TEMPLATE),
        ("paper_claim_session SCRATCH_TEMPLATE", paper_claim_session.SCRATCH_TEMPLATE),
    ):
        if unexpected_open in text or unexpected_open_scoped in text:
            raise RuntimeError(f"{label} unexpectedly contains ProductFree open directives")
    _, scratch = run_loop.formalize_to_scratch(
        theorem_name="thm_test_scratch_imports_000001",
        stmt="True",
        mode="proof",
        proof_text="trivial",
        counterexample_text="",
    )
    if expected_import not in scratch:
        raise RuntimeError("formalize_to_scratch output is missing Derived import")
    if unexpected_open in scratch or unexpected_open_scoped in scratch:
        raise RuntimeError("formalize_to_scratch output unexpectedly contains ProductFree open directives")
    _, scratch_with_prelude_import = run_loop.formalize_to_scratch(
        theorem_name="thm_test_scratch_imports_000002",
        stmt="True",
        mode="proof",
        proof_text="trivial",
        counterexample_text="",
        prelude_code="import Mathlib\n\nabbrev LocalAlias := True",
    )
    if scratch_with_prelude_import.count("import Mathlib\n") != 1:
        raise RuntimeError("formalize_to_scratch duplicated import Mathlib from prelude_code")
    if "abbrev LocalAlias := True" not in scratch_with_prelude_import:
        raise RuntimeError("formalize_to_scratch dropped prelude body after import normalization")
    print("scratch template imports test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
