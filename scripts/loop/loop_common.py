from __future__ import annotations

import time
from datetime import datetime
from pathlib import Path


def build_retry_deadline(budget_sec: int | None) -> float | None:
    if budget_sec is None:
        return None
    return time.monotonic() + max(1, budget_sec)


def remaining_retry_budget_sec(deadline: float | None) -> int | None:
    if deadline is None:
        return None
    remaining = int(deadline - time.monotonic())
    return max(0, remaining)


def update_same_fingerprint_streak(
    *,
    last_fingerprint: str,
    current_fingerprint: str,
    current_streak: int,
) -> tuple[str, int]:
    if not current_fingerprint:
        return "", 0
    if current_fingerprint == last_fingerprint:
        return last_fingerprint, current_streak + 1
    return current_fingerprint, 1


def prover_response_fingerprint(
    *,
    result: str,
    proof_sketch: str,
    counterexample_text: str,
) -> str:
    return " || ".join(
        [
            result.strip(),
            " ".join(proof_sketch.strip().split()),
            " ".join(counterexample_text.strip().split()),
        ]
    )


def iso_timestamp_now() -> str:
    return datetime.now().astimezone().isoformat(timespec="seconds")


def monotonic_duration_ms(started_at: float) -> int:
    return int((time.monotonic() - started_at) * 1000)


def build_run_id(kind: str = "loop") -> str:
    return f"{time.strftime('%Y%m%d-%H%M%S')}-{kind}"


def build_run_artifact_paths(data_dir: Path, run_id: str) -> dict[str, Path]:
    run_dir = data_dir / "runs" / run_id
    return {
        "run_dir": run_dir,
        "summary": run_dir / "summary.json",
        "theory_state_history": run_dir / "theory_state_history.jsonl",
        "phase_attempts": run_dir / "phase_attempts.jsonl",
        "problem_nodes": run_dir / "problem_nodes.jsonl",
        "theorem_nodes": run_dir / "theorem_nodes.jsonl",
        "lineage_edges": run_dir / "lineage_edges.jsonl",
    }
