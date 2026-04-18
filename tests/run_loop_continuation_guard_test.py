from __future__ import annotations

import json
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
        data_dir.mkdir(parents=True, exist_ok=True)
        scratch_file = tmp / "Scratch.lean"
        derived_file = tmp / "Derived.lean"
        preview_file = tmp / "Derived.refactored.preview.lean"
        reviewed_file = tmp / "Derived.refactored.reviewed.lean"
        memory_file = loop_dir / "formalization_memory.json"
        theory_state_file = loop_dir / "theory_state.json"

        write_jsonl_atomic(
            loop_dir / "open_problems.jsonl",
            [
                {
                    "id": "op_000061",
                    "stmt": "frontier",
                    "src": "generated",
                    "priority": "unknown",
                    "priority_rationale": "",
                    "failure_count": 0,
                }
            ],
        )
        write_jsonl_atomic(
            loop_dir / "archived_problems.jsonl",
            [
                {
                    "id": "op_000024",
                    "stmt": "archived",
                    "src": "generated",
                    "priority": "unknown",
                    "priority_rationale": "",
                    "failure_count": 2,
                }
            ],
        )
        write_jsonl_atomic(loop_dir / "solved_problems.jsonl", [{"id": "op_000007", "stmt": "solved", "thm": "thm"}])
        write_jsonl_atomic(loop_dir / "counterexamples.jsonl", [{"id": "op_000041", "stmt": "cex"}])
        (loop_dir / "theorem_reuse_memory.json").write_text('{"entries":[{"candidate_id":"x"}]}\n', encoding="utf-8")
        theory_state_file.write_text(json.dumps({"summary_basis": {"open_problem_count": 1}}, indent=2) + "\n", encoding="utf-8")
        memory_file.write_text('{"op_000061":[{"result":"stuck"}]}\n', encoding="utf-8")
        scratch_file.write_text("scratch before\n", encoding="utf-8")
        derived_file.write_text("derived before\n", encoding="utf-8")
        preview_file.write_text("preview before\n", encoding="utf-8")
        reviewed_file.write_text("reviewed before\n", encoding="utf-8")

        snapshot = run_loop.capture_continuation_runtime_snapshot(
            data_dir=data_dir,
            formalization_memory_file=memory_file,
            scratch_file=scratch_file,
            derived_file=derived_file,
            derived_cleanup_files=(preview_file, reviewed_file),
        )

        write_jsonl_atomic(loop_dir / "archived_problems.jsonl", [])
        write_jsonl_atomic(loop_dir / "solved_problems.jsonl", [])
        write_jsonl_atomic(loop_dir / "counterexamples.jsonl", [])
        write_jsonl_atomic(loop_dir / "open_problems.jsonl", [{"id": "op_000001", "stmt": "seed"}])
        (loop_dir / "theorem_reuse_memory.json").write_text('{"entries":[]}\n', encoding="utf-8")
        theory_state_file.unlink(missing_ok=True)
        memory_file.write_text("{}\n", encoding="utf-8")
        scratch_file.write_text("scratch reset\n", encoding="utf-8")
        derived_file.write_text("derived reset\n", encoding="utf-8")
        preview_file.unlink(missing_ok=True)
        reviewed_file.unlink(missing_ok=True)

        try:
            run_loop.guard_against_unexpected_continuation_reset(
                data_dir=data_dir,
                snapshot=snapshot,
            )
        except RuntimeError as exc:
            if "restored the pre-run snapshot" not in str(exc):
                raise RuntimeError(f"unexpected guard error: {exc}")
        else:
            raise RuntimeError("continuation guard should have raised after destructive reset")

        archived_rows = run_loop.read_jsonl(loop_dir / "archived_problems.jsonl")
        solved_rows = run_loop.read_jsonl(loop_dir / "solved_problems.jsonl")
        counter_rows = run_loop.read_jsonl(loop_dir / "counterexamples.jsonl")
        if len(archived_rows) != 1 or len(solved_rows) != 1 or len(counter_rows) != 1:
            raise RuntimeError("continuation guard did not restore queue history files")
        if theory_state_file.read_text(encoding="utf-8").strip() == "":
            raise RuntimeError("continuation guard did not restore theory_state.json")
        if derived_file.read_text(encoding="utf-8") != "derived before\n":
            raise RuntimeError("continuation guard did not restore Derived.lean")
        if scratch_file.read_text(encoding="utf-8") != "scratch before\n":
            raise RuntimeError("continuation guard did not restore Scratch.lean")

    print("run loop continuation guard test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
