from __future__ import annotations

import argparse
import json
import math
import re
import sys
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
SCRIPTS_ROOT = SCRIPT_DIR.parent
scripts_root_str = str(SCRIPTS_ROOT)
if scripts_root_str not in sys.path:
    sys.path.insert(0, scripts_root_str)

from common import write_json_atomic


DEFAULT_DERIVED_FILE = Path("AutomatedTheoryConstruction/Derived.lean")
DEFAULT_DEPS_FILE = Path("data/pipeline_artifacts/derived-deps.json")
DEFAULT_OUTPUT_FILE = Path("data/pipeline_artifacts/derived-chunk-plan.json")

DECL_PATTERN = re.compile(r"^(theorem|lemma|def|abbrev|inductive|structure)\s+([^\s:({]+)", re.MULTILINE)
THEOREM_KINDS = {"theorem", "lemma"}


def _round_float(value: float) -> float:
    return round(float(value), 6)


def load_json(path: Path) -> Any:
    if not path.exists():
        raise ValueError(f"File not found: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def parse_declaration_entries(derived_text: str) -> list[dict[str, Any]]:
    declarations: list[dict[str, Any]] = []
    for match in DECL_PATTERN.finditer(derived_text):
        declarations.append(
            {
                "kind": match.group(1),
                "short_name": match.group(2),
                "name": f"AutomatedTheoryConstruction.{match.group(2)}",
                "line": derived_text.count("\n", 0, match.start()) + 1,
            }
        )
    if not declarations:
        raise ValueError("Derived file did not contain any supported declarations")
    return declarations


def parse_declaration_order(derived_text: str) -> list[dict[str, Any]]:
    entries = parse_declaration_entries(derived_text)
    grouped: list[dict[str, Any]] = []
    pending_prefix_entries: list[dict[str, Any]] = []

    def build_group(members: list[dict[str, Any]], *, anchor: dict[str, Any]) -> dict[str, Any]:
        return {
            "kind": anchor["kind"],
            "short_name": anchor["short_name"],
            "name": anchor["name"],
            "line": int(members[0]["line"]),
            "anchor_line": int(anchor["line"]),
            "member_names": [str(member["name"]) for member in members],
            "member_kinds": [str(member["kind"]) for member in members],
        }

    for entry in entries:
        if str(entry["kind"]) in THEOREM_KINDS:
            members = pending_prefix_entries + [entry]
            grouped.append(build_group(members, anchor=entry))
            pending_prefix_entries = []
            continue
        pending_prefix_entries.append(entry)

    for entry in pending_prefix_entries:
        grouped.append(build_group([entry], anchor=entry))
    return grouped


def load_declaration_order(derived_file: Path) -> list[dict[str, Any]]:
    return parse_declaration_order(derived_file.read_text(encoding="utf-8"))


def _normalize_dependency_rows(raw_rows: Any) -> list[dict[str, Any]]:
    if not isinstance(raw_rows, list):
        raise ValueError("dependency file must contain a JSON list")
    normalized: list[dict[str, Any]] = []
    for row in raw_rows:
        if not isinstance(row, dict):
            raise ValueError("dependency rows must be objects")
        name = str(row.get("name", "")).strip()
        if not name:
            raise ValueError("dependency row is missing a name")
        references_raw = row.get("references", [])
        if not isinstance(references_raw, list):
            raise ValueError(f"dependency row references must be a list: {name}")
        seen_refs: set[str] = set()
        references: list[str] = []
        for ref in references_raw:
            ref_name = str(ref).strip()
            if not ref_name or ref_name in seen_refs:
                continue
            seen_refs.add(ref_name)
            references.append(ref_name)
        normalized.append({"name": name, "references": references})
    return normalized


def load_dependency_rows(deps_file: Path) -> list[dict[str, Any]]:
    return _normalize_dependency_rows(load_json(deps_file))


def build_internal_edges(
    declarations: list[dict[str, Any]],
    dependency_rows: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], dict[str, int]]:
    order_names = [decl["name"] for decl in declarations]
    order_set = set(order_names)
    dependency_name_set = {row["name"] for row in dependency_rows}

    missing_from_deps = [name for name in order_names if name not in dependency_name_set]
    extra_in_deps = [name for name in dependency_name_set if name not in order_set]
    if missing_from_deps or extra_in_deps:
        details: list[str] = []
        if missing_from_deps:
            preview = ", ".join(missing_from_deps[:8])
            details.append(f"missing_from_deps={preview}")
        if extra_in_deps:
            preview = ", ".join(sorted(extra_in_deps)[:8])
            details.append(f"extra_in_deps={preview}")
        raise ValueError("Derived declarations and dependency rows do not match: " + "; ".join(details))

    order_index = {name: index for index, name in enumerate(order_names)}
    edges: list[dict[str, Any]] = []
    ignored_external_reference_count = 0
    ignored_forward_reference_count = 0
    ignored_self_reference_count = 0

    for row in dependency_rows:
        source_name = row["name"]
        source_index = order_index[source_name]
        for target_name in row["references"]:
            if target_name not in order_index:
                ignored_external_reference_count += 1
                continue
            target_index = order_index[target_name]
            if target_index == source_index:
                ignored_self_reference_count += 1
                continue
            if target_index > source_index:
                ignored_forward_reference_count += 1
                continue
            distance = source_index - target_index
            weight = 1.0 / (1.0 + float(distance))
            edges.append(
                {
                    "source": source_name,
                    "target": target_name,
                    "source_index": source_index,
                    "target_index": target_index,
                    "distance": distance,
                    "weight": weight,
                }
            )

    return edges, {
        "ignored_external_reference_count": ignored_external_reference_count,
        "ignored_forward_reference_count": ignored_forward_reference_count,
        "ignored_self_reference_count": ignored_self_reference_count,
    }


def compute_boundary_loads(node_count: int, edges: list[dict[str, Any]]) -> list[float]:
    if node_count <= 1:
        return []
    diff = [0.0] * node_count
    for edge in edges:
        start = int(edge["target_index"])
        end = int(edge["source_index"])
        if start < 0 or end <= start:
            continue
        weight = float(edge["weight"])
        diff[start] += weight
        diff[end] -= weight
    boundary_loads: list[float] = []
    running = 0.0
    for boundary_index in range(node_count - 1):
        running += diff[boundary_index]
        boundary_loads.append(running)
    return boundary_loads


def _size_penalty(size: int, *, min_nodes: int, max_nodes: int, target_nodes: int) -> float:
    if size <= 0:
        return math.inf
    penalty = 0.0
    if size < min_nodes:
        penalty += float((min_nodes - size) ** 2)
    if size > max_nodes:
        penalty += float((size - max_nodes) ** 2)
    penalty += 0.05 * abs(size - target_nodes)
    return penalty


def compute_chunk_ranges(
    node_count: int,
    boundary_loads: list[float],
    *,
    min_nodes: int,
    max_nodes: int,
    target_nodes: int,
    cut_penalty: float,
) -> list[tuple[int, int]]:
    if node_count <= 0:
        return []
    costs = [math.inf] * (node_count + 1)
    previous = [-1] * (node_count + 1)
    costs[0] = 0.0

    for end in range(1, node_count + 1):
        for start in range(0, end):
            size = end - start
            penalty = _size_penalty(size, min_nodes=min_nodes, max_nodes=max_nodes, target_nodes=target_nodes)
            if math.isinf(penalty):
                continue
            cut_cost = 0.0
            if start > 0:
                cut_cost = float(boundary_loads[start - 1]) + float(cut_penalty)
            candidate = costs[start] + penalty + cut_cost
            if candidate < costs[end]:
                costs[end] = candidate
                previous[end] = start

    if previous[node_count] < 0:
        raise ValueError("failed to compute a valid chunk partition")

    ranges: list[tuple[int, int]] = []
    cursor = node_count
    while cursor > 0:
        start = previous[cursor]
        if start < 0:
            raise ValueError("failed to reconstruct chunk partition")
        ranges.append((start, cursor - 1))
        cursor = start
    ranges.reverse()
    return ranges


def build_chunk_plan(
    *,
    derived_file: Path,
    deps_file: Path,
    output_file: Path | None = None,
    min_nodes: int = 6,
    max_nodes: int = 14,
    target_nodes: int | None = None,
    cut_penalty: float = 0.25,
) -> dict[str, Any]:
    if min_nodes <= 0:
        raise ValueError("min_nodes must be positive")
    if max_nodes < min_nodes:
        raise ValueError("max_nodes must be >= min_nodes")
    if target_nodes is None:
        target_nodes = (min_nodes + max_nodes) // 2
    if target_nodes <= 0:
        raise ValueError("target_nodes must be positive")

    declarations = load_declaration_order(derived_file)
    dependency_rows = load_dependency_rows(deps_file)
    edges, ignored_counts = build_internal_edges(declarations, dependency_rows)
    boundary_loads = compute_boundary_loads(len(declarations), edges)
    chunk_ranges = compute_chunk_ranges(
        len(declarations),
        boundary_loads,
        min_nodes=min_nodes,
        max_nodes=max_nodes,
        target_nodes=target_nodes,
        cut_penalty=cut_penalty,
    )

    clusters: list[dict[str, Any]] = []
    for index, (start_index, end_index) in enumerate(chunk_ranges, start=1):
        nodes = declarations[start_index : end_index + 1]
        clusters.append(
            {
                "chunk_id": f"chunk_{index:03d}",
                "start_index": start_index,
                "end_index": end_index,
                "size": len(nodes),
                "start_line": nodes[0]["line"],
                "end_line": nodes[-1]["line"],
                "node_names": [node["name"] for node in nodes],
                "left_cut_load": None if start_index == 0 else _round_float(boundary_loads[start_index - 1]),
                "right_cut_load": None if end_index >= len(declarations) - 1 else _round_float(boundary_loads[end_index]),
            }
        )

    plan = {
        "plan_version": 1,
        "source_file": str(derived_file),
        "deps_file": str(deps_file),
        "summary": (
            f"{len(clusters)} chunks over {len(declarations)} declarations "
            f"using {len(edges)} internal dependencies"
        ),
        "parameters": {
            "min_nodes": min_nodes,
            "max_nodes": max_nodes,
            "target_nodes": target_nodes,
            "cut_penalty": _round_float(cut_penalty),
        },
        "node_count": len(declarations),
        "internal_edge_count": len(edges),
        **ignored_counts,
        "boundary_loads": [
            {
                "after_index": boundary_index,
                "after_name": declarations[boundary_index]["name"],
                "before_name": declarations[boundary_index + 1]["name"],
                "load": _round_float(load),
            }
            for boundary_index, load in enumerate(boundary_loads)
        ],
        "clusters": clusters,
    }
    if output_file is not None:
        write_json_atomic(output_file, plan)
    return plan


def main() -> None:
    parser = argparse.ArgumentParser(description="Plan contiguous dependency-aware chunks for AutomatedTheoryConstruction/Derived.lean")
    parser.add_argument("--derived-file", default=str(DEFAULT_DERIVED_FILE))
    parser.add_argument("--deps-file", default=str(DEFAULT_DEPS_FILE))
    parser.add_argument("--output-file", default=str(DEFAULT_OUTPUT_FILE))
    parser.add_argument("--min-nodes", type=int, default=6)
    parser.add_argument("--max-nodes", type=int, default=14)
    parser.add_argument("--target-nodes", type=int)
    parser.add_argument("--cut-penalty", type=float, default=0.25)
    args = parser.parse_args()

    plan = build_chunk_plan(
        derived_file=Path(args.derived_file),
        deps_file=Path(args.deps_file),
        output_file=Path(args.output_file),
        min_nodes=args.min_nodes,
        max_nodes=args.max_nodes,
        target_nodes=args.target_nodes,
        cut_penalty=args.cut_penalty,
    )
    print(json.dumps({"status": "ok", "output_file": args.output_file, "chunk_count": len(plan["clusters"]), "node_count": plan["node_count"]}))


if __name__ == "__main__":
    main()
