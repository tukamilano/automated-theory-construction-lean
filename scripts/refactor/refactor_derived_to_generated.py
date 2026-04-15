from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
SCRIPTS_ROOT = SCRIPT_DIR.parent
scripts_root_str = str(SCRIPTS_ROOT)
if scripts_root_str not in sys.path:
    sys.path.insert(0, scripts_root_str)

from atc_paths import loop_theorem_reuse_memory_path
from atc_paths import refactor_chunk_plan_path
from extract_derived_dependencies import extract_derived_dependencies
from generated_library import DEFAULT_GENERATED_CATALOG
from generated_library import DEFAULT_GENERATED_MANIFEST
from generated_library import DEFAULT_GENERATED_ROOT
from generated_library import ensure_generated_scaffold
from generated_library import iter_generated_chunk_files
from generated_library import render_generated_chunk
from generated_library import write_generated_catalog
from generated_library import write_generated_manifest
from plan_derived_chunks import DEFAULT_DEPS_FILE
from plan_derived_chunks import build_chunk_plan


DERIVED_TEMPLATE = (
    "import Mathlib\n"
    "import AutomatedTheoryConstruction.Theory\n\n"
    "import AutomatedTheoryConstruction.Generated.Manifest\n\n"
    "set_option autoImplicit false\n\n"
    "namespace AutomatedTheoryConstruction\n\n"
    "-- Verified theorems are appended here by scripts/append_derived.py.\n"
    "-- Keep any short theorem docstrings/comments here instead of a separate metadata index.\n\n"
    "end AutomatedTheoryConstruction\n"
)

REPO_ROOT = SCRIPTS_ROOT.parent
DEFAULT_DERIVED_FILE = Path("AutomatedTheoryConstruction/Derived.lean")
DEFAULT_PLAN_FILE = refactor_chunk_plan_path(Path("data"))
SLUG_TOKEN_PATTERN = re.compile(r"[A-Za-z][A-Za-z0-9']*")
SLUG_STOPWORDS = {
    "thm",
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "inductive",
    "structure",
    "iff",
    "is",
    "of",
    "to",
    "from",
    "and",
    "or",
    "self",
    "forward",
    "backward",
    "exact",
    "complete",
    "matches",
    "state",
    "step",
    "accepts",
    "recognizes",
    "bound",
    "same",
}
CAMEL_TOKEN_PATTERN = re.compile(r"[A-Z]?[a-z]+|[A-Z]+(?=[A-Z]|$)|\d+")


def _print_progress(event: str, **fields: Any) -> None:
    timestamp = time.strftime("%Y-%m-%dT%H:%M:%S%z")
    parts = [f"[materialize] {timestamp}", f"event={event}"]
    for key, value in fields.items():
        if value in (None, "", []):
            continue
        parts.append(f"{key}={value}")
    print(" ".join(parts), file=sys.stderr, flush=True)


def _resolve_generated_paths(
    *,
    derived_file: Path,
    generated_root: Path | None,
    manifest_file: Path | None,
    catalog_file: Path | None,
) -> tuple[Path, Path, Path]:
    resolved_root = generated_root or (derived_file.parent / "Generated")
    resolved_manifest = manifest_file or (resolved_root / "Manifest.lean")
    resolved_catalog = catalog_file or (resolved_root / "catalog.json")
    return resolved_root, resolved_manifest, resolved_catalog


def _collect_declaration_spans(derived_text: str) -> list[dict[str, Any]]:
    from plan_derived_chunks import parse_declaration_order

    declarations = parse_declaration_order(derived_text)
    lines = derived_text.splitlines()
    line_starts = [0]
    for index, char in enumerate(derived_text):
        if char == "\n":
            line_starts.append(index + 1)
    total_lines = derived_text.count("\n") + 1
    namespace_end_line = None
    for index, line in enumerate(lines, start=1):
        if line.strip() == "end AutomatedTheoryConstruction":
            namespace_end_line = index
    if namespace_end_line is None:
        raise ValueError("Derived file is missing `end AutomatedTheoryConstruction`")

    def line_offset(line_number: int) -> int:
        if line_number <= 0:
            return 0
        if line_number - 1 >= len(line_starts):
            return len(derived_text)
        return line_starts[line_number - 1]

    def attached_start_line(decl_line: int) -> int:
        cursor = decl_line - 2
        while cursor >= 0 and not lines[cursor].strip():
            cursor -= 1
        if cursor < 0 or not lines[cursor].strip().endswith("-/"):
            return decl_line
        while cursor >= 0:
            if "/--" in lines[cursor]:
                return cursor + 1
            cursor -= 1
        return decl_line

    for decl in declarations:
        start_line = int(decl["line"])
        decl["body_start_line"] = attached_start_line(start_line)
        decl["start_offset"] = line_offset(int(decl["body_start_line"]))

    for index, decl in enumerate(declarations):
        start_line = int(decl["body_start_line"])
        next_start_offset = (
            int(declarations[index + 1]["start_offset"])
            if index + 1 < len(declarations)
            else line_offset(namespace_end_line)
        )
        end_line = (
            int(declarations[index + 1]["body_start_line"]) - 1
            if index + 1 < len(declarations)
            else namespace_end_line - 1
        )
        decl["start_line"] = start_line
        decl["end_line"] = end_line
        decl["end_offset"] = next_start_offset
    return declarations


def _chunk_slug(node_names: list[str], *, used_slugs: set[str]) -> str:
    scores: dict[str, int] = {}
    first_seen: dict[str, int] = {}
    order = 0
    for full_name in node_names:
        short_name = full_name.rsplit(".", 1)[-1]
        pieces: list[str] = []
        for token in short_name.split("_"):
            pieces.extend(CAMEL_TOKEN_PATTERN.findall(token) or [token])
        for token in pieces:
            lowered = token.strip().lower()
            if not lowered or lowered in SLUG_STOPWORDS or lowered.isdigit():
                continue
            if re.fullmatch(r"\d+", lowered):
                continue
            if lowered not in first_seen:
                first_seen[lowered] = order
                order += 1
            scores[lowered] = scores.get(lowered, 0) + 1
    ordered_tokens = sorted(scores, key=lambda token: (-scores[token], first_seen[token], token))
    base_tokens = ordered_tokens[:3] or ["chunk"]
    candidate = "_".join(base_tokens)
    if candidate not in used_slugs:
        used_slugs.add(candidate)
        return candidate
    suffix = 2
    while f"{candidate}_{suffix}" in used_slugs:
        suffix += 1
    candidate = f"{candidate}_{suffix}"
    used_slugs.add(candidate)
    return candidate


def _slice_chunk_body(derived_text: str, declarations: list[dict[str, Any]], start_name: str, end_name: str) -> str:
    by_name = {decl["name"]: decl for decl in declarations}
    start_decl = by_name[start_name]
    end_decl = by_name[end_name]
    return derived_text[start_decl["start_offset"] : end_decl["end_offset"]].strip() + "\n"


def _extract_declaration_blocks(source_text: str) -> list[str]:
    try:
        declarations = _collect_declaration_spans(source_text)
    except ValueError as exc:
        if "supported declarations" in str(exc):
            return []
        raise
    blocks: list[str] = []
    for decl in declarations:
        block = source_text[int(decl["start_offset"]) : int(decl["end_offset"])].strip()
        if block:
            blocks.append(block)
    return blocks


def _render_materialized_derived(blocks: list[str]) -> str:
    body = "\n\n".join(blocks).strip()
    parts = [
        "import Mathlib",
        "import AutomatedTheoryConstruction.Theory",
        "",
        "set_option autoImplicit false",
        "",
        "namespace AutomatedTheoryConstruction",
        "",
        "open Mathling.Lambek.ProductFree",
        "open scoped Mathling.Lambek.ProductFree",
        "",
    ]
    if body:
        parts.append(body)
        parts.append("")
    parts.append("end AutomatedTheoryConstruction")
    parts.append("")
    return "\n".join(parts)


def _materialize_library_source(*, generated_root: Path, derived_file: Path) -> str:
    blocks: list[str] = []
    for chunk_file in iter_generated_chunk_files(generated_root):
        blocks.extend(_extract_declaration_blocks(chunk_file.read_text(encoding="utf-8")))
    if derived_file.exists():
        blocks.extend(_extract_declaration_blocks(derived_file.read_text(encoding="utf-8")))
    return _render_materialized_derived(blocks)


def _run_manifest_build(timeout_sec: int | None) -> dict[str, Any]:
    try:
        completed = subprocess.run(
            ["lake", "build", "AutomatedTheoryConstruction.Generated.Manifest"],
            cwd=str(REPO_ROOT),
            check=False,
            capture_output=True,
            text=True,
            timeout=None if timeout_sec in (None, 0) else timeout_sec,
        )
    except subprocess.TimeoutExpired as exc:
        stdout_text = exc.stdout if isinstance(exc.stdout, str) else ""
        stderr_text = exc.stderr if isinstance(exc.stderr, str) else ""
        detail = "\n".join(part for part in (stdout_text, stderr_text) if part).strip()
        return {
            "success": False,
            "detail": f"manifest build timed out after {timeout_sec}s\n{detail}".strip(),
            "returncode": None,
        }
    detail = "\n".join(part for part in (completed.stdout, completed.stderr) if part).strip()
    return {
        "success": completed.returncode == 0,
        "detail": detail,
        "returncode": completed.returncode,
    }


def _verify_manifest(timeout_sec: int | None) -> None:
    result = _run_manifest_build(timeout_sec)
    if not bool(result.get("success", False)):
        raise RuntimeError(f"manifest verification failed: {result.get('detail', '')}".strip())


def materialize_derived_to_generated(
    *,
    derived_file: Path,
    deps_file: Path,
    theory_file: Path,
    theorem_reuse_memory_file: Path,
    generated_root: Path | None,
    manifest_file: Path | None,
    catalog_file: Path | None,
    plan_file: Path,
    min_nodes: int = 6,
    max_nodes: int = 14,
    target_nodes: int | None = None,
    cut_penalty: float = 0.25,
    reset_derived: bool = True,
    refresh_dependencies: bool = True,
    deps_depth: int = 1,
    verify_manifest: bool = True,
    generated_repair_verify_timeout: int | None = 300,
) -> dict[str, Any]:
    generated_root, manifest_file, catalog_file = _resolve_generated_paths(
        derived_file=derived_file,
        generated_root=generated_root,
        manifest_file=manifest_file,
        catalog_file=catalog_file,
    )
    _print_progress(
        "start",
        derived_file=derived_file,
        generated_root=generated_root,
    )
    dependency_report: dict[str, Any] | None = None
    if refresh_dependencies:
        materialized_source = _materialize_library_source(
            generated_root=generated_root,
            derived_file=derived_file,
        )
        derived_file.write_text(materialized_source, encoding="utf-8")
        dependency_report = extract_derived_dependencies(
            derived_file=derived_file,
            output_file=deps_file,
            depth=deps_depth,
        )
        derived_text = materialized_source
    else:
        derived_text = _materialize_library_source(
            generated_root=generated_root,
            derived_file=derived_file,
        )
        derived_file.write_text(derived_text, encoding="utf-8")
    declarations = _collect_declaration_spans(derived_text)
    plan = build_chunk_plan(
        derived_file=derived_file,
        deps_file=deps_file,
        output_file=plan_file,
        min_nodes=min_nodes,
        max_nodes=max_nodes,
        target_nodes=target_nodes,
        cut_penalty=cut_penalty,
    )

    ensure_generated_scaffold(
        generated_root=generated_root,
        manifest_file=manifest_file,
        catalog_file=catalog_file,
    )

    for stale_file in generated_root.glob("*.lean"):
        if stale_file.name == "Manifest.lean":
            continue
        stale_file.unlink(missing_ok=True)

    catalog_chunks: list[dict[str, Any]] = []
    import_modules: list[str] = []
    previous_module: str | None = None
    used_slugs: set[str] = set()

    for index, cluster in enumerate(plan["clusters"], start=1):
        chunk_id = f"C{index:04d}"
        slug = _chunk_slug(cluster["node_names"], used_slugs=used_slugs)
        file_stem = f"{chunk_id}_{slug}"
        module_name = f"AutomatedTheoryConstruction.Generated.{file_stem}"
        output_file = generated_root / f"{file_stem}.lean"
        body = _slice_chunk_body(
            derived_text,
            declarations,
            cluster["node_names"][0],
            cluster["node_names"][-1],
        )
        output_file.write_text(
            render_generated_chunk(prior_module=previous_module, body=body),
            encoding="utf-8",
        )
        catalog_chunks.append(
            {
                "chunk_id": chunk_id,
                "slug": slug,
                "module_name": module_name,
                "file": str(output_file),
                "source_file": str(derived_file),
                "start_line": cluster["start_line"],
                "end_line": cluster["end_line"],
                "size": cluster["size"],
                "node_names": cluster["node_names"],
                "prior_module": previous_module,
            }
        )
        import_modules.append(module_name)
        previous_module = module_name

    write_generated_manifest(manifest_file, import_modules=import_modules)
    write_generated_catalog(catalog_file, chunks=catalog_chunks)
    if verify_manifest:
        _verify_manifest(generated_repair_verify_timeout)

    if reset_derived:
        derived_file.write_text(DERIVED_TEMPLATE, encoding="utf-8")

    should_run_final_manifest_build = bool(verify_manifest)
    final_manifest_build = (
        _run_manifest_build(generated_repair_verify_timeout)
        if should_run_final_manifest_build
        else {"success": True, "detail": "", "returncode": 0}
    )
    report = {
        "status": "ok" if bool(final_manifest_build.get("success", False)) else "error",
        "source_file": str(derived_file),
        "generated_root": str(generated_root),
        "manifest_file": str(manifest_file),
        "catalog_file": str(catalog_file),
        "plan_file": str(plan_file),
        "chunk_count": len(catalog_chunks),
        "reset_derived": reset_derived,
        "refresh_dependencies": refresh_dependencies,
        "deps_depth": deps_depth,
        "verify_manifest": verify_manifest,
        "final_manifest_build_success": bool(final_manifest_build.get("success", False)),
        "final_manifest_build_detail": str(final_manifest_build.get("detail", "")),
    }
    if dependency_report is not None:
        report["deps_file"] = dependency_report["output_file"]
    _print_progress("finish", status=report["status"], chunk_count=len(catalog_chunks))
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description="Refactor Derived.lean into Generated/C0001.lean style chunks.")
    parser.add_argument("--derived-file", default=str(DEFAULT_DERIVED_FILE))
    parser.add_argument("--deps-file", default=str(DEFAULT_DEPS_FILE))
    parser.add_argument("--theory-file", default="AutomatedTheoryConstruction/Theory.lean")
    parser.add_argument("--theorem-reuse-memory-file", default=str(loop_theorem_reuse_memory_path(Path("data"))))
    parser.add_argument("--generated-root")
    parser.add_argument("--manifest-file")
    parser.add_argument("--catalog-file")
    parser.add_argument("--plan-file", default=str(DEFAULT_PLAN_FILE))
    parser.add_argument("--min-nodes", type=int, default=6)
    parser.add_argument("--max-nodes", type=int, default=14)
    parser.add_argument("--target-nodes", type=int)
    parser.add_argument("--cut-penalty", type=float, default=0.25)
    parser.add_argument("--reset-derived", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--refresh-dependencies", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--deps-depth", type=int, default=1)
    parser.add_argument("--verify-manifest", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--generated-repair-verify-timeout", type=int, default=300)
    args = parser.parse_args()

    report = materialize_derived_to_generated(
        derived_file=Path(args.derived_file),
        deps_file=Path(args.deps_file),
        theory_file=Path(args.theory_file),
        theorem_reuse_memory_file=Path(args.theorem_reuse_memory_file),
        generated_root=Path(args.generated_root) if args.generated_root else None,
        manifest_file=Path(args.manifest_file) if args.manifest_file else None,
        catalog_file=Path(args.catalog_file) if args.catalog_file else None,
        plan_file=Path(args.plan_file),
        min_nodes=args.min_nodes,
        max_nodes=args.max_nodes,
        target_nodes=args.target_nodes,
        cut_penalty=args.cut_penalty,
        reset_derived=bool(args.reset_derived),
        refresh_dependencies=bool(args.refresh_dependencies),
        deps_depth=args.deps_depth,
        verify_manifest=bool(args.verify_manifest),
        generated_repair_verify_timeout=args.generated_repair_verify_timeout,
    )
    print(json.dumps(report, ensure_ascii=False))


if __name__ == "__main__":
    main()
