from __future__ import annotations

import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "loop"))


import run_loop
from main_theorem import main_theorem_session


def main() -> int:
    expected_import = "import AutomatedTheoryConstruction.Generated.Manifest"
    tracked_scratch = REPO_ROOT / "AutomatedTheoryConstruction" / "Scratch.lean"
    tracked_derived = REPO_ROOT / "AutomatedTheoryConstruction" / "Derived.lean"
    if expected_import not in tracked_scratch.read_text(encoding="utf-8"):
        raise RuntimeError("tracked Scratch.lean is missing Generated.Manifest import")
    if expected_import not in tracked_derived.read_text(encoding="utf-8"):
        raise RuntimeError("tracked Derived.lean is missing Generated.Manifest import")
    if expected_import not in run_loop.SCRATCH_TEMPLATE:
        raise RuntimeError("run_loop SCRATCH_TEMPLATE is missing Generated.Manifest import")
    if expected_import not in run_loop.DERIVED_TEMPLATE:
        raise RuntimeError("run_loop DERIVED_TEMPLATE is missing Generated.Manifest import")
    if expected_import not in main_theorem_session.SCRATCH_TEMPLATE:
        raise RuntimeError("main_theorem_session SCRATCH_TEMPLATE is missing Generated.Manifest import")
    _, scratch = run_loop.formalize_to_scratch(
        theorem_name="thm_test_generated_manifest_000001",
        stmt="True",
        mode="proof",
        proof_text="trivial",
        counterexample_text="",
    )
    if expected_import not in scratch:
        raise RuntimeError("formalize_to_scratch output is missing Generated.Manifest import")
    print("scratch template generated manifest test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
