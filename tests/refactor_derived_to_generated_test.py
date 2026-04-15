from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "refactor"))


from generated_library import build_library_entries
from refactor_derived_to_generated import _chunk_slug
from refactor_derived_to_generated import materialize_derived_to_generated


def main() -> int:
    sample_slug = _chunk_slug(
        [
            "AutomatedTheoryConstruction.AtomicResidualState",
            "AutomatedTheoryConstruction.AtomicResidualGraphStep",
            "AutomatedTheoryConstruction.AtomicResidualGraphAccepts",
            "AutomatedTheoryConstruction.atomicResidualGraphAccepts_iff_atomicCandidateTree",
            "AutomatedTheoryConstruction.thm_residual_graph_recognizes_sequent_000062",
            "AutomatedTheoryConstruction.AtomicBranchLength",
            "AutomatedTheoryConstruction.thm_residual_atomic_branch_bound_000057",
        ],
        used_slugs=set(),
    )
    if sample_slug != "atomic_residual_graph":
        raise RuntimeError(f"unexpected camel-case slug: {sample_slug}")

    with tempfile.TemporaryDirectory() as tmp_dir:
        root = Path(tmp_dir)
        atc_dir = root / "AutomatedTheoryConstruction"
        generated_root = atc_dir / "Generated"
        atc_dir.mkdir(parents=True, exist_ok=True)
        derived_file = atc_dir / "Derived.lean"
        theory_file = atc_dir / "Theory.lean"
        deps_file = root / "derived-deps.json"
        plan_file = root / "derived-chunk-plan.json"
        theorem_reuse_memory_file = root / "theorem_reuse_memory.json"
        manifest_file = generated_root / "Manifest.lean"
        catalog_file = generated_root / "catalog.json"
        theory_file.write_text("import Mathlib\n", encoding="utf-8")
        theorem_reuse_memory_file.write_text("[]\n", encoding="utf-8")

        derived_file.write_text(
            """import Mathlib
import AutomatedTheoryConstruction.Theory

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

theorem alpha : True := by
  trivial

/-- beta docstring -/
theorem beta : True := by
  have h : True := alpha
  exact h

/-- gamma docstring -/
theorem gamma : True := by
  have h : True := beta
  exact h

/-- delta docstring -/
theorem delta : True := by
  trivial

theorem epsilon : True := by
  have h : True := delta
  exact h

theorem zeta : True := by
  have h : True := epsilon
  exact h

end AutomatedTheoryConstruction
""",
            encoding="utf-8",
        )
        deps_file.write_text(
            json.dumps(
                [
                    {"name": "AutomatedTheoryConstruction.alpha", "references": []},
                    {"name": "AutomatedTheoryConstruction.beta", "references": ["AutomatedTheoryConstruction.alpha"]},
                    {"name": "AutomatedTheoryConstruction.gamma", "references": ["AutomatedTheoryConstruction.beta"]},
                    {"name": "AutomatedTheoryConstruction.delta", "references": []},
                    {"name": "AutomatedTheoryConstruction.epsilon", "references": ["AutomatedTheoryConstruction.delta"]},
                    {"name": "AutomatedTheoryConstruction.zeta", "references": ["AutomatedTheoryConstruction.epsilon"]},
                ],
                ensure_ascii=False,
                indent=2,
            ),
            encoding="utf-8",
        )

        report = materialize_derived_to_generated(
            derived_file=derived_file,
            deps_file=deps_file,
            theory_file=theory_file,
            theorem_reuse_memory_file=theorem_reuse_memory_file,
            generated_root=None,
            manifest_file=None,
            catalog_file=None,
            plan_file=plan_file,
            min_nodes=2,
            max_nodes=4,
            target_nodes=3,
            cut_penalty=0.2,
            reset_derived=True,
            refresh_dependencies=False,
            verify_manifest=False,
        )
        if report["chunk_count"] != 2:
            raise RuntimeError(f"unexpected report: {report}")
        if Path(report["generated_root"]) != generated_root:
            raise RuntimeError(f"unexpected generated root: {report}")
        catalog = json.loads(catalog_file.read_text(encoding="utf-8"))
        chunk_files = [Path(chunk["file"]) for chunk in catalog["chunks"]]
        if len(chunk_files) != 2 or not all(path.exists() for path in chunk_files):
            raise RuntimeError(f"expected generated chunk files to exist: {catalog}")
        if not chunk_files[0].name.startswith("C0001_"):
            raise RuntimeError(f"unexpected first chunk file name: {chunk_files[0].name}")
        if not chunk_files[1].name.startswith("C0002_"):
            raise RuntimeError(f"unexpected second chunk file name: {chunk_files[1].name}")
        chunk_one = chunk_files[0]
        chunk_two = chunk_files[1]
        chunk_one_text = chunk_one.read_text(encoding="utf-8")
        chunk_two_text = chunk_two.read_text(encoding="utf-8")
        if "/-- delta docstring -/" in chunk_one_text:
            raise RuntimeError("next declaration docstring leaked into previous chunk")
        if "/-- delta docstring -/" not in chunk_two_text:
            raise RuntimeError("delta docstring was not attached to the second chunk")
        first_module = catalog["chunks"][0]["module_name"]
        second_module = catalog["chunks"][1]["module_name"]
        if f"import {first_module}" not in chunk_two_text:
            raise RuntimeError("expected second chunk to import the first chunk")
        if chunk_two_text.count("end AutomatedTheoryConstruction") != 1:
            raise RuntimeError("expected exactly one namespace end marker in the second chunk")
        manifest_text = manifest_file.read_text(encoding="utf-8")
        if f"import {first_module}" not in manifest_text:
            raise RuntimeError("manifest did not import the first chunk")
        if f"import {second_module}" not in manifest_text:
            raise RuntimeError("manifest did not import the second chunk")
        if [chunk["chunk_id"] for chunk in catalog["chunks"]] != ["C0001", "C0002"]:
            raise RuntimeError(f"unexpected catalog: {catalog}")
        derived_after = derived_file.read_text(encoding="utf-8")
        if "theorem alpha" in derived_after or "theorem zeta" in derived_after:
            raise RuntimeError("expected Derived.lean to be reset")
        if "open Mathling.Lambek.ProductFree" in derived_after:
            raise RuntimeError("reset Derived.lean unexpectedly contains ProductFree open")
        if "open scoped Mathling.Lambek.ProductFree" in derived_after:
            raise RuntimeError("reset Derived.lean unexpectedly contains scoped ProductFree open")
        library_entries = build_library_entries(generated_root=generated_root, derived_file=derived_file)
        theorem_names = [entry["theorem_name"] for entry in library_entries]
        if theorem_names != ["alpha", "beta", "gamma", "delta", "epsilon", "zeta"]:
            raise RuntimeError(f"unexpected library entries: {theorem_names}")

    with tempfile.TemporaryDirectory() as tmp_dir:
        root = Path(tmp_dir)
        atc_dir = root / "AutomatedTheoryConstruction"
        generated_root = atc_dir / "Generated"
        atc_dir.mkdir(parents=True, exist_ok=True)
        derived_file = atc_dir / "Derived.lean"
        theory_file = atc_dir / "Theory.lean"
        deps_file = root / "derived-deps.json"
        plan_file = root / "derived-chunk-plan.json"
        theorem_reuse_memory_file = root / "theorem_reuse_memory.json"
        theory_file.write_text("import Mathlib\n", encoding="utf-8")
        theorem_reuse_memory_file.write_text("[]\n", encoding="utf-8")
        derived_file.write_text(
            """import Mathlib
import AutomatedTheoryConstruction.Theory

set_option autoImplicit false

namespace AutomatedTheoryConstruction

theorem alpha : True := by
  trivial

theorem beta : True := by
  have h : True := alpha
  exact h

end AutomatedTheoryConstruction
""",
            encoding="utf-8",
        )
        deps_file.write_text(
            json.dumps(
                [
                    {"name": "AutomatedTheoryConstruction.alpha", "references": []},
                    {"name": "AutomatedTheoryConstruction.beta", "references": ["AutomatedTheoryConstruction.alpha"]},
                ],
                ensure_ascii=False,
                indent=2,
            ),
            encoding="utf-8",
        )
        completed = subprocess.run(
            [
                sys.executable,
                str(REPO_ROOT / "scripts" / "refactor" / "refactor_derived_to_generated.py"),
                "--derived-file",
                str(derived_file),
                "--deps-file",
                str(deps_file),
                "--theory-file",
                str(theory_file),
                "--theorem-reuse-memory-file",
                str(theorem_reuse_memory_file),
                "--plan-file",
                str(plan_file),
                "--min-nodes",
                "1",
                "--max-nodes",
                "2",
                "--no-refresh-dependencies",
                "--no-verify-manifest",
            ],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            check=False,
        )
        if completed.returncode != 0:
            raise RuntimeError(f"script entrypoint failed: stdout={completed.stdout!r} stderr={completed.stderr!r}")
        generated_files = sorted(path for path in generated_root.glob("*.lean") if path.name != "Manifest.lean")
        if len(generated_files) != 1 or not generated_files[0].name.startswith("C0001_"):
            raise RuntimeError("script entrypoint did not create Generated output")
        if '"chunk_count": 1' not in completed.stdout:
            raise RuntimeError(f"unexpected script stdout: {completed.stdout!r}")

    with tempfile.TemporaryDirectory() as tmp_dir:
        root = Path(tmp_dir)
        atc_dir = root / "AutomatedTheoryConstruction"
        generated_root = atc_dir / "Generated"
        atc_dir.mkdir(parents=True, exist_ok=True)
        derived_file = atc_dir / "Derived.lean"
        theory_file = atc_dir / "Theory.lean"
        deps_file = root / "derived-deps.json"
        plan_file = root / "derived-chunk-plan.json"
        theorem_reuse_memory_file = root / "theorem_reuse_memory.json"
        theory_file.write_text("import Mathlib\n", encoding="utf-8")
        theorem_reuse_memory_file.write_text("[]\n", encoding="utf-8")
        derived_file.write_text(
            """import Mathlib
import AutomatedTheoryConstruction.Theory

set_option autoImplicit false

namespace AutomatedTheoryConstruction

theorem alpha : True := by
  trivial

theorem beta : True := by
  trivial

theorem gamma : True := by
  have h : True := alpha
  exact h

theorem delta : True := by
  have h : True := gamma
  exact h

end AutomatedTheoryConstruction
""",
            encoding="utf-8",
        )
        deps_file.write_text(
            json.dumps(
                [
                    {"name": "AutomatedTheoryConstruction.alpha", "references": []},
                    {"name": "AutomatedTheoryConstruction.beta", "references": []},
                    {"name": "AutomatedTheoryConstruction.gamma", "references": ["AutomatedTheoryConstruction.alpha"]},
                    {"name": "AutomatedTheoryConstruction.delta", "references": ["AutomatedTheoryConstruction.gamma"]},
                ],
                ensure_ascii=False,
                indent=2,
            ),
            encoding="utf-8",
        )

        report = materialize_derived_to_generated(
            derived_file=derived_file,
            deps_file=deps_file,
            theory_file=theory_file,
            theorem_reuse_memory_file=theorem_reuse_memory_file,
            generated_root=None,
            manifest_file=None,
            catalog_file=None,
            plan_file=plan_file,
            min_nodes=2,
            max_nodes=4,
            target_nodes=3,
            cut_penalty=0.2,
            reset_derived=False,
            refresh_dependencies=False,
            verify_manifest=False,
            generated_repair_verify_timeout=30,
        )
        if not report["final_manifest_build_success"]:
            raise RuntimeError(f"expected final manifest build success: {report}")
        if report["chunk_count"] != 1:
            raise RuntimeError(f"unexpected report after no-pass run: {report}")

    print("refactor derived to generated test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
