from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))


from plan_derived_chunks import build_chunk_plan
from plan_derived_chunks import build_internal_edges
from plan_derived_chunks import compute_boundary_loads
from plan_derived_chunks import parse_declaration_order


def _write(path: Path, text: str) -> None:
    path.write_text(text, encoding="utf-8")


def main() -> int:
    with tempfile.TemporaryDirectory() as tmp_dir:
        tmp_path = Path(tmp_dir)
        derived_file = tmp_path / "Derived.lean"
        deps_file = tmp_path / "derived-deps.json"
        output_file = tmp_path / "derived-chunk-plan.json"

        _write(
            derived_file,
            """import Mathlib
import AutomatedTheoryConstruction.Theory

namespace AutomatedTheoryConstruction

theorem alpha : True := by
  trivial

theorem beta : True := by
  trivial

theorem gamma : True := by
  trivial

theorem delta : True := by
  trivial

theorem epsilon : True := by
  trivial

theorem zeta : True := by
  trivial

end AutomatedTheoryConstruction
""",
        )
        deps_payload = [
            {"name": "AutomatedTheoryConstruction.alpha", "references": ["Trans.trans"]},
            {"name": "AutomatedTheoryConstruction.beta", "references": ["AutomatedTheoryConstruction.alpha", "Trans.trans"]},
            {"name": "AutomatedTheoryConstruction.gamma", "references": ["AutomatedTheoryConstruction.beta"]},
            {
                "name": "AutomatedTheoryConstruction.delta",
                "references": ["AutomatedTheoryConstruction.alpha", "Trans.trans"],
            },
            {"name": "AutomatedTheoryConstruction.epsilon", "references": ["AutomatedTheoryConstruction.delta"]},
            {
                "name": "AutomatedTheoryConstruction.zeta",
                "references": ["AutomatedTheoryConstruction.epsilon", "AutomatedTheoryConstruction.zeta"],
            },
        ]
        deps_file.write_text(json.dumps(deps_payload, ensure_ascii=False, indent=2), encoding="utf-8")

        declarations = parse_declaration_order(derived_file.read_text(encoding="utf-8"))
        if [decl["short_name"] for decl in declarations] != ["alpha", "beta", "gamma", "delta", "epsilon", "zeta"]:
            raise RuntimeError(f"unexpected declaration order: {declarations}")

        edges, ignored_counts = build_internal_edges(declarations, deps_payload)
        if len(edges) != 5:
            raise RuntimeError(f"expected 5 internal edges, found {len(edges)}")
        if ignored_counts["ignored_external_reference_count"] != 3:
            raise RuntimeError(f"unexpected external reference count: {ignored_counts}")
        if ignored_counts["ignored_self_reference_count"] != 1:
            raise RuntimeError(f"unexpected self reference count: {ignored_counts}")

        boundary_loads = compute_boundary_loads(len(declarations), edges)
        expected_peak = max(boundary_loads)
        if expected_peak <= 0:
            raise RuntimeError(f"boundary loads were not computed: {boundary_loads}")
        if min(boundary_loads) != boundary_loads[2]:
            raise RuntimeError(f"expected a valley after gamma, loads={boundary_loads}")

        plan = build_chunk_plan(
            derived_file=derived_file,
            deps_file=deps_file,
            output_file=output_file,
            min_nodes=2,
            max_nodes=4,
            target_nodes=3,
            cut_penalty=0.2,
        )
        cluster_sizes = [cluster["size"] for cluster in plan["clusters"]]
        if cluster_sizes != [3, 3]:
            raise RuntimeError(f"unexpected cluster sizes: {cluster_sizes}")
        first_cluster_names = plan["clusters"][0]["node_names"]
        second_cluster_names = plan["clusters"][1]["node_names"]
        if first_cluster_names != [
            "AutomatedTheoryConstruction.alpha",
            "AutomatedTheoryConstruction.beta",
            "AutomatedTheoryConstruction.gamma",
        ]:
            raise RuntimeError(f"unexpected first cluster: {first_cluster_names}")
        if second_cluster_names != [
            "AutomatedTheoryConstruction.delta",
            "AutomatedTheoryConstruction.epsilon",
            "AutomatedTheoryConstruction.zeta",
        ]:
            raise RuntimeError(f"unexpected second cluster: {second_cluster_names}")
        if plan["clusters"][0]["right_cut_load"] != 0.25:
            raise RuntimeError(f"unexpected cut load: {plan['clusters'][0]}")
        if not output_file.exists():
            raise RuntimeError("expected output file to be written")

    print("derived chunk plan test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
