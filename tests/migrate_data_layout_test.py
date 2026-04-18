from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))


import migrate_data_layout


def main() -> int:
    with tempfile.TemporaryDirectory() as tmpdir:
        data_root = Path(tmpdir) / "data"
        data_root.mkdir(parents=True, exist_ok=True)
        (data_root / "open_problems.jsonl").write_text('{"id":"op_1"}\n', encoding="utf-8")
        (data_root / "theory_state.json").write_text('{"version":1}\n', encoding="utf-8")
        legacy_refactor_dir = data_root / "pipeline_artifacts"
        legacy_refactor_dir.mkdir(parents=True, exist_ok=True)
        (legacy_refactor_dir / "derived-deps.json").write_text("{}\n", encoding="utf-8")

        plans = migrate_data_layout.build_move_plan(data_root)
        errors = migrate_data_layout.validate_move_plan(plans)
        if errors:
            raise RuntimeError(f"unexpected validation errors: {errors}")

        migrate_data_layout.apply_move_plan(plans)
        migrate_data_layout.cleanup_empty_legacy_dirs(data_root)

        expected_paths = [
            data_root / "loop" / "open_problems.jsonl",
            data_root / "loop" / "theory_state.json",
            data_root / "refactor" / "derived-deps.json",
        ]
        for path in expected_paths:
            if not path.exists():
                raise RuntimeError(f"expected migrated path missing: {path}")
        if (data_root / "pipeline_artifacts").exists():
            raise RuntimeError("legacy pipeline_artifacts dir should have been removed after migration")

    with tempfile.TemporaryDirectory() as tmpdir:
        data_root = Path(tmpdir) / "data"
        data_root.mkdir(parents=True, exist_ok=True)
        source = data_root / "open_problems.jsonl"
        destination = data_root / "loop" / "open_problems.jsonl"
        source.write_text('{"id":"legacy"}\n', encoding="utf-8")
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text('{"id":"new"}\n', encoding="utf-8")

        plans = migrate_data_layout.build_move_plan(data_root)
        errors = migrate_data_layout.validate_move_plan(plans)
        if not errors:
            raise RuntimeError("expected conflict to be reported when destination content differs")
        report = migrate_data_layout.build_report(data_root=data_root, plans=plans, errors=errors, apply=False)
        if report.get("ok") is not False:
            raise RuntimeError(f"expected report ok=false on conflict, got {json.dumps(report)}")

    print("migrate data layout test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
