from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent


def copy_tree(src: Path, dst: Path) -> None:
    shutil.copytree(src, dst, dirs_exist_ok=True)


def copy_file(src: Path, dst: Path) -> None:
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst)


def stage_repo(dst_root: Path) -> None:
    for relative in (
        Path("lakefile.lean"),
        Path("lake-manifest.json"),
        Path("lean-toolchain"),
        Path("AutomatedTheoryConstruction.lean"),
    ):
        copy_file(REPO_ROOT / relative, dst_root / relative)

    for relative in (
        Path("AutomatedTheoryConstruction"),
        Path("scripts"),
        Path("prompts"),
    ):
        copy_tree(REPO_ROOT / relative, dst_root / relative)

    packages_src = REPO_ROOT / ".lake" / "packages"
    if not packages_src.exists():
        raise RuntimeError("missing .lake/packages; run lake build once before make smoke")

    lake_dir = dst_root / ".lake"
    lake_dir.mkdir(parents=True, exist_ok=True)
    os.symlink(packages_src, lake_dir / "packages")


def write_smoke_seed_file(dst_root: Path) -> None:
    seeds_path = dst_root / "AutomatedTheoryConstruction" / "seeds.jsonl"
    seed_row = {
        "id": "op_000001",
        "stmt": "∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], (⊠⊠(⊤ : α) ≐ ⊠(⊤ : α)) ↔ Nonempty (ACR.GödelFixpoint α)",
        "src": "smoke",
        "priority": "medium",
        "priority_rationale": "smoke fixture",
        "failure_count": 0,
    }
    seeds_path.write_text(json.dumps(seed_row, ensure_ascii=False) + "\n", encoding="utf-8")


def run_smoke_loop(dst_root: Path) -> None:
    cmd = [
        sys.executable,
        "scripts/atc_cli.py",
        "loop",
        "--worker-command",
        "python3 scripts/mock_worker.py",
        "--max-iterations",
        "1",
        "--skip-verify",
        "--main-theorem-interval",
        "0",
        "--priority-refresh-theorem-interval",
        "0",
    ]
    try:
        completed = subprocess.run(
            cmd,
            cwd=dst_root,
            check=False,
            capture_output=True,
            text=True,
            timeout=120,
        )
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError(
            "smoke loop timed out\n"
            f"stdout:\n{exc.stdout or ''}\n"
            f"stderr:\n{exc.stderr or ''}"
        ) from exc
    if completed.returncode != 0:
        raise RuntimeError(
            "smoke loop failed\n"
            f"stdout:\n{completed.stdout}\n"
            f"stderr:\n{completed.stderr}"
        )


def assert_smoke_outputs(dst_root: Path) -> None:
    data_dir = dst_root / "data"
    if not (data_dir / "open_problems.jsonl").exists():
        raise RuntimeError("smoke loop did not create data/open_problems.jsonl")
    if not (dst_root / "AutomatedTheoryConstruction" / "Scratch.lean").exists():
        raise RuntimeError("smoke loop did not create Scratch.lean")
    if not (dst_root / "AutomatedTheoryConstruction" / "Derived.lean").exists():
        raise RuntimeError("smoke loop did not create Derived.lean")

    summary_paths = sorted((data_dir / "runs").glob("*/summary.json"))
    if not summary_paths:
        raise RuntimeError("smoke loop did not create a run summary")

    summary = json.loads(summary_paths[-1].read_text(encoding="utf-8"))
    if summary.get("status") != "max_iterations_reached":
        raise RuntimeError(f"unexpected smoke summary status: {summary.get('status')}")


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="atc-smoke-") as temp_dir:
        dst_root = Path(temp_dir) / "repo"
        print(f"[smoke] staging isolated repo at {dst_root}", file=sys.stderr)
        stage_repo(dst_root)
        print("[smoke] writing seed fixture", file=sys.stderr)
        write_smoke_seed_file(dst_root)
        print("[smoke] running loop", file=sys.stderr)
        run_smoke_loop(dst_root)
        print("[smoke] checking outputs", file=sys.stderr)
        assert_smoke_outputs(dst_root)
    print("smoke test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
