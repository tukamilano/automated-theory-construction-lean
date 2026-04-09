from __future__ import annotations

import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))


from common import load_theory_context


def main() -> int:
    theory_file = REPO_ROOT / "AutomatedTheoryConstruction" / "Theory.lean"
    theory_files, _ = load_theory_context(theory_file, repo_root=REPO_ROOT)
    normalized = {path.resolve() for path in theory_files}

    required = {
        (REPO_ROOT / "AutomatedTheoryConstruction" / "Lambek" / "Basic.lean").resolve(),
        (REPO_ROOT / "AutomatedTheoryConstruction" / "Lambek" / "Decidable.lean").resolve(),
        (REPO_ROOT / "AutomatedTheoryConstruction" / "Lambek" / "Shallow" / "Basic.lean").resolve(),
        (REPO_ROOT / "AutomatedTheoryConstruction" / "Lambek" / "Left" / "Basic.lean").resolve(),
        (REPO_ROOT / "AutomatedTheoryConstruction" / "Lambek" / "Right" / "Basic.lean").resolve(),
    }

    missing = sorted(str(path.relative_to(REPO_ROOT)) for path in required if path not in normalized)
    if missing:
        raise RuntimeError(f"Theory.lean context is missing Lambek modules: {missing}")

    print("theory context imports test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
