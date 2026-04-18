from __future__ import annotations

import argparse
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "loop"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "refactor"))


import run_pipeline
from extract_theorem_type_alpha_groups import _build_harness_source


def test_harness_uses_defeq_function() -> None:
    source = _build_harness_source(
        target_import="AutomatedTheoryConstruction.Derived",
        extractor_source="def placeholder : Unit := ()",
        declaration_names=["AutomatedTheoryConstruction.foo"],
        output_file=Path("/tmp/out.json"),
        duplicate_function_name="duplicateTheoremTypeClustersDefEq",
    )
    if "duplicateTheoremTypeClustersDefEq targetDecls" not in source:
        raise RuntimeError(f"defeq harness should call defeq duplicate function, got:\n{source}")


def test_pipeline_command_propagates_equivalence_mode() -> None:
    args = argparse.Namespace(
        alpha_dedupe_report_file="report.json",
        alpha_dedupe_equivalence_mode="defeq",
    )
    cmd = run_pipeline.build_alpha_dedupe_command(
        args,
        input_file="in.lean",
        output_file="out.lean",
        alpha_source_file="alpha.lean",
        build_target="AutomatedTheoryConstruction.Derived",
    )
    if "--equivalence-mode" not in cmd:
        raise RuntimeError(f"pipeline alpha-dedupe command should include --equivalence-mode, got {cmd}")
    if cmd[cmd.index("--equivalence-mode") + 1] != "defeq":
        raise RuntimeError(f"pipeline alpha-dedupe command should preserve defeq mode, got {cmd}")


def main() -> int:
    test_harness_uses_defeq_function()
    test_pipeline_command_propagates_equivalence_mode()
    print("alpha dedupe equivalence mode test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
