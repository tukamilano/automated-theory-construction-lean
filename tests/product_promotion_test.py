from __future__ import annotations

import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "loop"))


from append_derived import promote_staging_to_product
from append_derived import reset_staging_derived_file
from derived_entries import extract_derived_theorem_entries
from theorem_store import DERIVED_TEMPLATE
from theorem_store import PRODUCT_TEMPLATE


def main() -> int:
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)
        product_file = tmp / "Product.lean"
        derived_file = tmp / "Derived.lean"

        product_file.write_text(
            PRODUCT_TEMPLATE.replace(
                "end AutomatedTheoryConstruction\n",
                "theorem stable_base : True := by\n  trivial\n\nend AutomatedTheoryConstruction\n",
            ),
            encoding="utf-8",
        )
        derived_file.write_text(
            DERIVED_TEMPLATE.replace(
                "end AutomatedTheoryConstruction\n",
                "theorem staged_delta : True := by\n  exact stable_base\n\nend AutomatedTheoryConstruction\n",
            ),
            encoding="utf-8",
        )

        entries_before = extract_derived_theorem_entries(derived_file)
        theorem_names_before = [entry["name"] for entry in entries_before]
        if theorem_names_before != ["stable_base", "staged_delta"]:
            raise RuntimeError(f"unexpected theorem inventory before promotion: {theorem_names_before}")

        promoted = promote_staging_to_product(product_file, derived_file)
        if not promoted:
            raise RuntimeError("expected promotion to append staged body into Product.lean")
        reset_staging_derived_file(derived_file)

        product_text = product_file.read_text(encoding="utf-8")
        derived_text = derived_file.read_text(encoding="utf-8")
        if "theorem staged_delta" not in product_text:
            raise RuntimeError("promoted theorem missing from Product.lean")
        if "theorem staged_delta" in derived_text:
            raise RuntimeError("Derived.lean should be reset after promotion")

        entries_after = extract_derived_theorem_entries(derived_file)
        theorem_names_after = [entry["name"] for entry in entries_after]
        if theorem_names_after != ["stable_base", "staged_delta"]:
            raise RuntimeError(f"unexpected theorem inventory after promotion: {theorem_names_after}")

    print("product promotion test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
