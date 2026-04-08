from __future__ import annotations

import ast
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
    seed_rows = [
        {
            "id": "op_000001",
            "stmt": "∀ {α : Type _}, True",
            "src": "smoke",
            "priority": "unknown",
            "priority_rationale": "",
            "failure_count": 0,
        },
        {
            "id": "op_000002",
            "stmt": "∀ {α : Type _} [Inhabited α], True ∧ True",
            "src": "smoke",
            "priority": "unknown",
            "priority_rationale": "",
            "failure_count": 0,
        },
    ]
    payload = "".join(json.dumps(row, ensure_ascii=False) + "\n" for row in seed_rows)
    seeds_path.write_text(payload, encoding="utf-8")


def write_mock_proof_worker(dst_root: Path) -> None:
    worker_path = dst_root / "scripts" / "mock_proof_worker.py"
    worker_path.write_text(
        """from __future__ import annotations

import json
import sys


def _read_request() -> dict[str, object]:
    return json.loads(sys.stdin.read())


def main() -> None:
    request = _read_request()
    task_type = str(request.get("task_type", ""))
    payload = request.get("payload", {})
    if not isinstance(payload, dict):
        raise ValueError("payload must be a JSON object")

    problem_id = str(payload.get("problem_id", ""))
    source_id = str(payload.get("source_id", ""))
    stmt = str(payload.get("stmt", "")).strip()
    prelude_name = f"smoke_helper_{problem_id}"
    prelude_code = f"abbrev {prelude_name} : Prop := True" if problem_id else ""

    if task_type == "prover_statement":
        theorem_stem = f"statement_target_{problem_id}_smoke" if problem_id else "statement_target"
        result_payload = {
            "problem_id": problem_id,
            "result": "ok" if stmt else "stuck",
            "statement_prelude_code": prelude_code if stmt else "",
            "lean_statement": stmt,
            "theorem_name_stem": theorem_stem,
            "docstring_summary": "Smoke proof.",
            "notes": "mock_proof_worker: echoed statement",
        }
    elif task_type == "prover":
        result_payload = {
            "problem_id": problem_id,
            "result": "proof",
            "proof_sketch": "Smoke proof.",
            "counterexample_text": "",
        }
    elif task_type in {"formalize", "repair"}:
        result_payload = {
            "problem_id": problem_id,
            "result": "proof",
            "proof_sketch": "Smoke proof.",
            "prelude_code": prelude_code,
            "proof_text": "aesop",
            "counterexample_text": "",
        }
    elif task_type == "post_solve_opportunity":
        result_payload = {
            "source_id": source_id,
            "opportunity": None,
        }
    elif task_type == "refactor_derived":
        derived_code = str(payload.get("derived_code", "")).strip()
        result_payload = {
            "result": "noop",
            "refactored_code": derived_code,
            "summary": "mock_proof_worker: no refactor changes",
            "change_notes": [],
            "touched_theorems": [],
        }
    elif task_type == "prioritize_open_problems":
        tracked_problems = payload.get("tracked_problems", [])
        if not isinstance(tracked_problems, list):
            raise ValueError("tracked_problems must be a list")
        result_payload = {
            "priorities": [
                {
                    "problem_id": str(item.get("problem_id", "")),
                    "priority": "high",
                    "rationale": "mock_proof_worker: refresh priorities",
                }
                for item in tracked_problems
                if isinstance(item, dict) and str(item.get("problem_id", "")).strip()
            ],
            "theory_snapshot": "Mock smoke theory: the active queue is being solved directly, so the snapshot only records that the fixture is intentionally biased toward immediate solvability.",
            "next_direction": {
                "label": "smoke_direction",
                "guidance": "Prefer continuing the direct-solvability smoke fixture path.",
                "rationale": "The smoke worker is intentionally configured to solve the queued problems immediately.",
            },
            "desired_summary_changes": [],
            "current_bottlenecks": [],
            "overexplored_patterns": [],
            "missing_bridges": [],
            "agenda_pressure": [],
        }
    elif task_type == "main_theorem_suggest":
        result_payload = {
            "candidate_id": str(payload.get("candidate_id", "")),
            "result": "stuck",
            "selected_problem_id": "",
            "theorem_name_stem": "",
            "docstring_summary": "",
            "rationale": "mock_proof_worker: no main theorem suggestion",
            "supporting_theorems": [],
            "missing_lemmas": [],
        }
    elif task_type == "main_theorem_plan":
        result_payload = {
            "candidate_id": str(payload.get("candidate_id", "")),
            "result": "stuck",
            "plan_summary": "mock_proof_worker: no plan generated",
            "proof_sketch": "",
            "supporting_theorems": [],
            "intermediate_lemmas": [],
            "notes": "mock_proof_worker: no main theorem proof plan",
        }
    else:
        raise ValueError(f"unsupported task_type: {task_type}")

    raw_model_output = json.dumps(result_payload, ensure_ascii=False)
    response = {
        "result_payload": result_payload,
        "worker_meta": {
            "worker": "mock_proof_worker",
            "task_type": task_type,
            "raw_model_output": raw_model_output,
        },
        "error": None,
    }
    sys.stdout.write(json.dumps(response, ensure_ascii=False))


if __name__ == "__main__":
    main()
""",
        encoding="utf-8",
    )


def run_smoke_loop(
    dst_root: Path,
    *,
    max_iterations: int = 2,
    parallel_sessions: int = 2,
    priority_refresh_theorem_interval: int = 0,
    timeout_sec: int = 420,
) -> subprocess.CompletedProcess[str]:
    cmd = [
        sys.executable,
        "scripts/atc_cli.py",
        "loop",
        "--worker-command",
        "python3 scripts/mock_proof_worker.py",
        "--max-iterations",
        str(max_iterations),
        "--parallel-sessions",
        str(parallel_sessions),
        "--skip-verify",
        "--main-theorem-interval",
        "0",
        "--priority-refresh-theorem-interval",
        str(priority_refresh_theorem_interval),
    ]
    try:
        completed = subprocess.run(
            cmd,
            cwd=dst_root,
            check=False,
            capture_output=True,
            text=True,
            timeout=timeout_sec,
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
    return completed


def assert_smoke_outputs(dst_root: Path) -> None:
    data_dir = dst_root / "data"
    if not (data_dir / "open_problems.jsonl").exists():
        raise RuntimeError("smoke loop did not create data/open_problems.jsonl")
    if not (data_dir / "theory_state.json").exists():
        raise RuntimeError("smoke loop did not create data/theory_state.json")
    if not (dst_root / "AutomatedTheoryConstruction" / "Scratch.lean").exists():
        raise RuntimeError("smoke loop did not create Scratch.lean")
    if not (dst_root / "AutomatedTheoryConstruction" / "Scratch.loop.lean").exists():
        raise RuntimeError("smoke loop did not create Scratch.loop.lean")
    if not (dst_root / "AutomatedTheoryConstruction" / "Scratch.loop.002.lean").exists():
        raise RuntimeError("smoke loop did not create Scratch.loop.002.lean")
    if not (dst_root / "AutomatedTheoryConstruction" / "Derived.lean").exists():
        raise RuntimeError("smoke loop did not create Derived.lean")

    summary_paths = sorted((data_dir / "runs").glob("*/summary.json"))
    if not summary_paths:
        raise RuntimeError("smoke loop did not create a run summary")

    summary = json.loads(summary_paths[-1].read_text(encoding="utf-8"))
    if summary.get("status") not in {"max_iterations_reached", "no_open_problems"}:
        raise RuntimeError(f"unexpected smoke summary status: {summary.get('status')}")
    theory_state_history_path = summary_paths[-1].with_name("theory_state_history.jsonl")
    if not theory_state_history_path.exists():
        raise RuntimeError("smoke loop did not create runs/<run_id>/theory_state_history.jsonl")
    theory_state = json.loads((data_dir / "theory_state.json").read_text(encoding="utf-8"))
    if theory_state.get("next_direction", {}).get("label") != "smoke_direction":
        raise RuntimeError(f"unexpected theory_state next_direction: {theory_state}")
    theory_state_history_rows = [
        json.loads(line)
        for line in theory_state_history_path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    if not theory_state_history_rows:
        raise RuntimeError("theory_state_history.jsonl is empty")
    if theory_state_history_rows[0].get("theory_state", {}).get("summary_basis", {}).get("derived_theorem_count") != 0:
        raise RuntimeError(f"unexpected initial theory_state history head: {theory_state_history_rows[0]}")
    if theory_state_history_rows[-1].get("theory_state", {}).get("next_direction", {}).get("label") != "smoke_direction":
        raise RuntimeError(f"unexpected theory_state history tail: {theory_state_history_rows[-1]}")

    open_rows = [
        json.loads(line)
        for line in (data_dir / "open_problems.jsonl").read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    solved_rows = [
        json.loads(line)
        for line in (data_dir / "solved_problems.jsonl").read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    if open_rows:
        raise RuntimeError(f"smoke loop left open problems behind: {open_rows}")
    if len(solved_rows) != 2:
        raise RuntimeError(f"expected 2 solved problems, got {len(solved_rows)}")

    derived_text = (dst_root / "AutomatedTheoryConstruction" / "Derived.lean").read_text(encoding="utf-8")
    if "thm_statement_target_op_000001_smoke_000001" not in derived_text or "thm_statement_target_op_000002_smoke_000002" not in derived_text:
        raise RuntimeError("smoke loop did not append solved theorems to Derived.lean")
    if "abbrev smoke_helper_op_000001 : Prop := True" not in derived_text:
        raise RuntimeError("smoke loop did not append prelude_code for op_000001")
    if "abbrev smoke_helper_op_000002 : Prop := True" not in derived_text:
        raise RuntimeError("smoke loop did not append prelude_code for op_000002")


def assert_priority_refresh_report(completed: subprocess.CompletedProcess[str]) -> None:
    reports: list[dict[str, object]] = []
    for raw_line in completed.stdout.splitlines():
        line = raw_line.strip()
        if not line or not line.startswith("{"):
            continue
        try:
            payload = ast.literal_eval(line)
        except (SyntaxError, ValueError):
            continue
        if isinstance(payload, dict) and "priority_refresh_ran" in payload:
            reports.append(payload)

    if not reports:
        raise RuntimeError(f"did not capture any loop reports from stdout:\n{completed.stdout}")
    if not any(bool(report.get("priority_refresh_ran", False)) for report in reports):
        raise RuntimeError(f"priority refresh never reported success:\n{completed.stdout}")


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="atc-smoke-") as temp_dir:
        dst_root = Path(temp_dir) / "repo"
        print(f"[smoke] staging isolated repo at {dst_root}", file=sys.stderr)
        stage_repo(dst_root)
        print("[smoke] writing seed fixture", file=sys.stderr)
        write_smoke_seed_file(dst_root)
        print("[smoke] writing proof worker fixture", file=sys.stderr)
        write_mock_proof_worker(dst_root)
        print("[smoke] running loop", file=sys.stderr)
        run_smoke_loop(dst_root)
        print("[smoke] checking outputs", file=sys.stderr)
        assert_smoke_outputs(dst_root)
    with tempfile.TemporaryDirectory(prefix="atc-priority-refresh-") as temp_dir:
        dst_root = Path(temp_dir) / "repo"
        print(f"[priority-refresh] staging isolated repo at {dst_root}", file=sys.stderr)
        stage_repo(dst_root)
        print("[priority-refresh] writing seed fixture", file=sys.stderr)
        write_smoke_seed_file(dst_root)
        print("[priority-refresh] writing proof worker fixture", file=sys.stderr)
        write_mock_proof_worker(dst_root)
        print("[priority-refresh] running loop", file=sys.stderr)
        completed = run_smoke_loop(
            dst_root,
            parallel_sessions=1,
            priority_refresh_theorem_interval=1,
        )
        print("[priority-refresh] checking reports", file=sys.stderr)
        assert_priority_refresh_report(completed)
    with tempfile.TemporaryDirectory(prefix="atc-priority-refresh-parallel-") as temp_dir:
        dst_root = Path(temp_dir) / "repo"
        print(f"[priority-refresh-parallel] staging isolated repo at {dst_root}", file=sys.stderr)
        stage_repo(dst_root)
        print("[priority-refresh-parallel] writing seed fixture", file=sys.stderr)
        write_smoke_seed_file(dst_root)
        print("[priority-refresh-parallel] writing proof worker fixture", file=sys.stderr)
        write_mock_proof_worker(dst_root)
        print("[priority-refresh-parallel] running loop", file=sys.stderr)
        completed = run_smoke_loop(
            dst_root,
            parallel_sessions=2,
            priority_refresh_theorem_interval=1,
        )
        print("[priority-refresh-parallel] checking reports", file=sys.stderr)
        assert_priority_refresh_report(completed)
    print("smoke test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
