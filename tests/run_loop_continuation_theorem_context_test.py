from __future__ import annotations

import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "loop"))


import run_loop
from common import write_jsonl_atomic


def main() -> int:
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)
        data_dir = tmp / "data"
        loop_dir = data_dir / "loop"
        atc_dir = tmp / "AutomatedTheoryConstruction"
        loop_dir.mkdir(parents=True, exist_ok=True)
        atc_dir.mkdir(parents=True, exist_ok=True)

        derived_file = atc_dir / "Derived.lean"
        derived_file.write_text(run_loop.DERIVED_TEMPLATE, encoding="utf-8")
        write_jsonl_atomic(loop_dir / "solved_problems.jsonl", [{"id": "op_000001", "stmt": "solved", "thm": "thm"}])

        try:
            run_loop.validate_continuation_theorem_context(
                data_dir=data_dir,
                derived_file=derived_file,
            )
        except RuntimeError as exc:
            message = str(exc)
            if "Continuation run requested with solved problems already recorded" not in message:
                raise RuntimeError(f"unexpected validation error: {message}")
        else:
            raise RuntimeError("expected continuation theorem-context validation to fail")

    print("run loop continuation theorem context test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
