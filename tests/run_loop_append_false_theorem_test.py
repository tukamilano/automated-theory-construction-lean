from __future__ import annotations

import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))


import run_loop


def main() -> int:
    scratch_code = """import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

theorem thm_example_is_false : ¬(False) := by
  intro h
  exact h

end AutomatedTheoryConstruction
"""
    scratch_with_sorry = """import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

theorem thm_example_bad_is_false : ¬(False) := by
  sorry

end AutomatedTheoryConstruction
"""

    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)
        scratch_path = tmp / "Scratch.lean"
        derived_path = tmp / "Derived.lean"
        scratch_path.write_text(scratch_code, encoding="utf-8")
        derived_path.write_text(
            "import Mathlib\n"
            "import AutomatedTheoryConstruction.Theory\n\n"
            "namespace AutomatedTheoryConstruction\n\n"
            "end AutomatedTheoryConstruction\n",
            encoding="utf-8",
        )

        original_run = run_loop.subprocess.run
        try:
            def fake_run(*_args, **_kwargs):
                class Result:
                    returncode = 0
                    stdout = ""
                    stderr = ""

                return Result()

            run_loop.subprocess.run = fake_run
            appended = run_loop.append_verified_theorem_from_scratch(
                scratch_path=scratch_path,
                derived_file=derived_path,
                derived_entries=[],
                docstring="negative theorem should still be recorded",
            )
        finally:
            run_loop.subprocess.run = original_run

        if "theorem thm_example_is_false" not in appended:
            raise RuntimeError("false theorem was not returned from append_verified_theorem_from_scratch")

        derived_text = derived_path.read_text(encoding="utf-8")
        if "theorem thm_example_is_false" not in derived_text:
            raise RuntimeError("false theorem was not appended to Derived.lean")

        bad_scratch_path = tmp / "ScratchBad.lean"
        bad_scratch_path.write_text(scratch_with_sorry, encoding="utf-8")
        rejected = run_loop.append_verified_theorem_from_scratch(
            scratch_path=bad_scratch_path,
            derived_file=derived_path,
            derived_entries=[],
            docstring="sorry-backed theorem should be rejected",
        )
        if rejected:
            raise RuntimeError("sorry-backed theorem should not be returned from append_verified_theorem_from_scratch")

        derived_text = derived_path.read_text(encoding="utf-8")
        if "theorem thm_example_bad_is_false" in derived_text:
            raise RuntimeError("sorry-backed false theorem should not be appended to Derived.lean")

    print("run loop append false theorem test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
