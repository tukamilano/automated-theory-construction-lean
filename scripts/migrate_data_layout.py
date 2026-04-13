from __future__ import annotations

import argparse
import json
import shutil
import sys
from dataclasses import dataclass
from pathlib import Path

from atc_paths import ARCHIVED_PROBLEMS_FILENAME
from atc_paths import COUNTEREXAMPLES_FILENAME
from atc_paths import EXPAND_CANDIDATES_FILENAME
from atc_paths import FORMALIZATION_MEMORY_FILENAME
from atc_paths import OPEN_PROBLEMS_FILENAME
from atc_paths import PAPER_CLAIM_DIRNAME
from atc_paths import PAPER_CLAIM_REJECTION_MEMORY_FILENAME
from atc_paths import REFRACTOR_DIRNAME
from atc_paths import SOLVED_PROBLEMS_FILENAME
from atc_paths import THEOREM_REUSE_MEMORY_FILENAME
from atc_paths import THEORY_STATE_FILENAME
from common import LEGACY_DEFERRED_PROBLEMS_FILENAME
from common import LEGACY_PRUNED_OPEN_PROBLEMS_FILENAME


@dataclass(frozen=True)
class MovePlan:
    source: Path
    destination: Path


def _legacy_loop_moves(data_root: Path) -> list[MovePlan]:
    return [
        MovePlan(data_root / OPEN_PROBLEMS_FILENAME, data_root / "loop" / OPEN_PROBLEMS_FILENAME),
        MovePlan(data_root / ARCHIVED_PROBLEMS_FILENAME, data_root / "loop" / ARCHIVED_PROBLEMS_FILENAME),
        MovePlan(data_root / SOLVED_PROBLEMS_FILENAME, data_root / "loop" / SOLVED_PROBLEMS_FILENAME),
        MovePlan(data_root / COUNTEREXAMPLES_FILENAME, data_root / "loop" / COUNTEREXAMPLES_FILENAME),
        MovePlan(data_root / FORMALIZATION_MEMORY_FILENAME, data_root / "loop" / FORMALIZATION_MEMORY_FILENAME),
        MovePlan(data_root / THEOREM_REUSE_MEMORY_FILENAME, data_root / "loop" / THEOREM_REUSE_MEMORY_FILENAME),
        MovePlan(data_root / PAPER_CLAIM_REJECTION_MEMORY_FILENAME, data_root / "loop" / PAPER_CLAIM_REJECTION_MEMORY_FILENAME),
        MovePlan(data_root / THEORY_STATE_FILENAME, data_root / "loop" / THEORY_STATE_FILENAME),
        MovePlan(data_root / EXPAND_CANDIDATES_FILENAME, data_root / "loop" / EXPAND_CANDIDATES_FILENAME),
        MovePlan(data_root / LEGACY_DEFERRED_PROBLEMS_FILENAME, data_root / "loop" / LEGACY_DEFERRED_PROBLEMS_FILENAME),
        MovePlan(data_root / LEGACY_PRUNED_OPEN_PROBLEMS_FILENAME, data_root / "loop" / LEGACY_PRUNED_OPEN_PROBLEMS_FILENAME),
    ]


def _legacy_dir_moves(data_root: Path, source_dir_name: str, destination_dir: Path) -> list[MovePlan]:
    source_dir = data_root / source_dir_name
    if not source_dir.exists():
        return []
    return [
        MovePlan(path, destination_dir / path.name)
        for path in sorted(source_dir.iterdir())
        if path.is_file()
    ]


def build_move_plan(data_root: Path) -> list[MovePlan]:
    plans = [plan for plan in _legacy_loop_moves(data_root) if plan.source.exists()]
    plans.extend(_legacy_dir_moves(data_root, "pipeline_artifacts", data_root / REFRACTOR_DIRNAME))
    plans.extend(_legacy_dir_moves(data_root, "paper-claim-session", data_root / PAPER_CLAIM_DIRNAME / "paper-claim-session"))
    legacy_root_paper_claim_event = data_root / "paper-claim.events.jsonl"
    if legacy_root_paper_claim_event.exists():
        plans.append(
            MovePlan(
                legacy_root_paper_claim_event,
                data_root / PAPER_CLAIM_DIRNAME / "paper-claim-session" / "paper_claim.events.jsonl",
            )
        )
    return plans


def _paths_conflict(source: Path, destination: Path) -> bool:
    if not destination.exists():
        return False
    if source.is_file() and destination.is_file():
        return source.read_bytes() != destination.read_bytes()
    return True


def validate_move_plan(plans: list[MovePlan]) -> list[str]:
    errors: list[str] = []
    seen_destinations: set[Path] = set()
    for plan in plans:
        if plan.destination in seen_destinations:
            errors.append(f"duplicate destination planned: {plan.destination}")
            continue
        seen_destinations.add(plan.destination)
        if _paths_conflict(plan.source, plan.destination):
            errors.append(f"destination already exists with different content: {plan.destination}")
    return errors


def apply_move_plan(plans: list[MovePlan]) -> None:
    for plan in plans:
        if not plan.source.exists():
            continue
        plan.destination.parent.mkdir(parents=True, exist_ok=True)
        if plan.destination.exists():
            if plan.source.is_file() and plan.destination.is_file() and plan.source.read_bytes() == plan.destination.read_bytes():
                plan.source.unlink(missing_ok=True)
                continue
            raise RuntimeError(f"refusing to overwrite existing destination: {plan.destination}")
        shutil.move(str(plan.source), str(plan.destination))


def cleanup_empty_legacy_dirs(data_root: Path) -> None:
    for path in (
        data_root / "pipeline_artifacts",
        data_root / "paper-claim-session",
    ):
        if path.exists() and path.is_dir() and not any(path.iterdir()):
            path.rmdir()


def build_report(*, data_root: Path, plans: list[MovePlan], errors: list[str], apply: bool) -> dict[str, object]:
    return {
        "data_root": str(data_root),
        "apply": apply,
        "move_count": len(plans),
        "moves": [
            {
                "source": str(plan.source),
                "destination": str(plan.destination),
            }
            for plan in plans
        ],
        "errors": errors,
        "ok": not errors,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Migrate legacy data/* artifacts into role-specific subdirectories.")
    parser.add_argument("--data-root", default="data")
    parser.add_argument("--apply", action="store_true", help="Perform the move instead of only printing the plan.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    data_root = Path(args.data_root)
    plans = build_move_plan(data_root)
    errors = validate_move_plan(plans)
    report = build_report(data_root=data_root, plans=plans, errors=errors, apply=bool(args.apply))
    sys.stdout.write(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    if errors:
        return 1
    if args.apply:
        apply_move_plan(plans)
        cleanup_empty_legacy_dirs(data_root)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
