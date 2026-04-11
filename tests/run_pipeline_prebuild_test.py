from __future__ import annotations

import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))


import run_pipeline


DISABLE_REFACTOR_FLAGS = [
    "--no-run-refactor-pass-1_5",
    "--no-run-refactor-pass-2",
]


def collect_stage_names(extra_argv: list[str]) -> list[str]:
    recorded: list[str] = []
    original_argv = sys.argv[:]
    original_run_stage = run_pipeline.run_stage
    try:
        sys.argv = ["run_pipeline.py", "--dry-run", *DISABLE_REFACTOR_FLAGS, *extra_argv]

        def fake_run_stage(
            name: str,
            cmd: list[str],
            *,
            dry_run: bool,
            capture_output: bool = False,
        ):
            recorded.append(name)
            return None

        run_pipeline.run_stage = fake_run_stage
        exit_code = run_pipeline.main()
        if exit_code != 0:
            raise RuntimeError(f"run_pipeline.main() returned {exit_code}")
    finally:
        run_pipeline.run_stage = original_run_stage
        sys.argv = original_argv
    return recorded


def collect_stage_commands(extra_argv: list[str]) -> dict[str, list[str]]:
    recorded: dict[str, list[str]] = {}
    original_argv = sys.argv[:]
    original_run_stage = run_pipeline.run_stage
    try:
        sys.argv = ["run_pipeline.py", "--dry-run", *DISABLE_REFACTOR_FLAGS, *extra_argv]

        def fake_run_stage(
            name: str,
            cmd: list[str],
            *,
            dry_run: bool,
            capture_output: bool = False,
        ):
            recorded[name] = list(cmd)
            return None

        run_pipeline.run_stage = fake_run_stage
        exit_code = run_pipeline.main()
        if exit_code != 0:
            raise RuntimeError(f"run_pipeline.main() returned {exit_code}")
    finally:
        run_pipeline.run_stage = original_run_stage
        sys.argv = original_argv
    return recorded


def main() -> int:
    continued_names = collect_stage_names(["--no-initialize-on-start", "--no-run-seed"])
    if continued_names[:3] != [
        "lean-prebuild:AutomatedTheoryConstruction.Theory",
        "lean-prebuild:AutomatedTheoryConstruction.Derived",
        "main-loop",
    ]:
        raise RuntimeError(f"continuation pipeline should prebuild before loop, got {continued_names}")

    fresh_names = collect_stage_names([])
    if fresh_names[:2] != ["seed-generation", "main-loop"]:
        raise RuntimeError(f"fresh pipeline should seed then loop, got {fresh_names}")
    if any(name.startswith("lean-prebuild:") for name in fresh_names):
        raise RuntimeError(f"fresh pipeline should not duplicate lake build, got {fresh_names}")

    seedless_names = collect_stage_names(["--no-run-seed"])
    if seedless_names[:3] != [
        "lean-prebuild:AutomatedTheoryConstruction.Theory",
        "lean-prebuild:AutomatedTheoryConstruction.Derived",
        "main-loop",
    ]:
        raise RuntimeError(f"seedless pipeline should prebuild before loop, got {seedless_names}")

    commands = collect_stage_commands(["--seed-count", "7"])
    loop_cmd = commands.get("main-loop", [])
    if "--seed-count" not in loop_cmd:
        raise RuntimeError(f"main-loop command should receive --seed-count, got {loop_cmd}")
    if loop_cmd[loop_cmd.index("--seed-count") + 1] != "7":
        raise RuntimeError(f"main-loop command should preserve seed-count value, got {loop_cmd}")

    print("run pipeline prebuild test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
