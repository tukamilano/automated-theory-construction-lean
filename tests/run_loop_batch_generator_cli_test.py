from __future__ import annotations

import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "loop"))


import run_loop


def main() -> int:
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)
        output_file = tmp / "generated.jsonl"
        output_file.write_text("", encoding="utf-8")

        captured: dict[str, object] = {}
        original_run = run_loop.subprocess.run
        try:
            def fake_run(cmd, **kwargs):
                captured["cmd"] = list(cmd)

                class Result:
                    returncode = 0
                    stdout = ""
                    stderr = ""

                return Result()

            run_loop.subprocess.run = fake_run
            rows, error = run_loop.run_batch_generator_subprocess(
                repo_root=REPO_ROOT,
                theory_file=REPO_ROOT / "AutomatedTheoryConstruction" / "Theory.lean",
                derived_file=REPO_ROOT / "AutomatedTheoryConstruction" / "Derived.lean",
                output_file=output_file,
                seed_count=3,
            )
        finally:
            run_loop.subprocess.run = original_run

        if rows != [] or error:
            raise RuntimeError(f"unexpected batch generator result: rows={rows}, error={error}")

        cmd = captured.get("cmd")
        if not isinstance(cmd, list):
            raise RuntimeError("subprocess command was not captured")
        if "--no-initialize-runtime-state" not in cmd:
            raise RuntimeError(f"missing --no-initialize-runtime-state in command: {cmd}")
        if any(part == "--initialize-runtime-state=false" for part in cmd):
            raise RuntimeError(f"deprecated boolean flag style still present: {cmd}")

    print("run loop batch generator cli test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
