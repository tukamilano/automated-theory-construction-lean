from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path
from typing import Any


def verify_scratch(problem_id: str, mode: str, scratch_file: Path, timeout_sec: int) -> dict[str, Any]:
    cmd = ["lake", "env", "lean", str(scratch_file)]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout_sec)
    return {
        "problem_id": problem_id,
        "success": proc.returncode == 0,
        "mode": mode,
        "stderr": proc.stderr,
        "stdout": proc.stdout,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Verify Lean code in Scratch.lean")
    parser.add_argument("--problem-id", required=True)
    parser.add_argument("--mode", required=True, choices=["proof", "counterexample"])
    parser.add_argument("--scratch-file", default="AutomatedTheoryConstruction/Scratch.lean")
    parser.add_argument("--timeout", type=int, default=60)
    args = parser.parse_args()

    result = verify_scratch(
        problem_id=args.problem_id,
        mode=args.mode,
        scratch_file=Path(args.scratch_file),
        timeout_sec=args.timeout,
    )
    print(json.dumps(result, ensure_ascii=True))


if __name__ == "__main__":
    main()
