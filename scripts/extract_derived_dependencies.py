from __future__ import annotations

import argparse
import json
import subprocess
import tempfile
from pathlib import Path
from typing import Any

from plan_derived_chunks import DEFAULT_DEPS_FILE
from plan_derived_chunks import DEFAULT_DERIVED_FILE
from plan_derived_chunks import parse_declaration_order


REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_EXTRACTOR_FILE = REPO_ROOT / "LeanTools/DependencyExtractor.lean"
DEFAULT_BUILD_TARGET = "AutomatedTheoryConstruction.Derived"


def _lean_string_literal(text: str) -> str:
    return json.dumps(text)


def _lean_name_literal(full_name: str) -> str:
    return f"`{full_name}"


def _build_harness_source(
    *,
    derived_import: str,
    extractor_source: str,
    declaration_names: list[str],
    output_file: Path,
    depth: int,
) -> str:
    names_block = "\n".join(f"  {_lean_name_literal(name)}," for name in declaration_names)
    return (
        f"import {derived_import}\n\n"
        f"{extractor_source.rstrip()}\n\n"
        "def derivedDecls : List Name := [\n"
        f"{names_block}\n"
        "]\n\n"
        "#eval do\n"
        f"  let g <- getUsedConstantGraph derivedDecls {int(depth)}\n"
        "  let js <- serializeList g\n"
        f"  let _ <- writeJsonToFile {_lean_string_literal(str(output_file))} js\n"
    )


def _normalize_dependency_payload(
    payload: Any,
    *,
    declaration_names: list[str],
    output_file: Path,
) -> list[dict[str, Any]]:
    if not isinstance(payload, list):
        raise ValueError("dependency extractor did not return a JSON list")
    by_name: dict[str, dict[str, Any]] = {}
    for row in payload:
        if not isinstance(row, dict):
            raise ValueError("dependency row must be an object")
        name = str(row.get("name", "")).strip()
        if not name:
            raise ValueError("dependency row is missing a name")
        by_name[name] = {
            "name": name,
            "constCategory": str(row.get("constCategory", "")).strip(),
            "constType": str(row.get("constType", "")).strip(),
            "references": [str(item).strip() for item in row.get("references", []) if str(item).strip()],
        }
    missing = [name for name in declaration_names if name not in by_name]
    if missing:
        preview = ", ".join(missing[:8])
        raise ValueError(f"dependency extractor omitted declarations: {preview}")
    normalized = [by_name[name] for name in declaration_names]
    output_file.write_text(json.dumps(normalized, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return normalized


def extract_derived_dependencies(
    *,
    derived_file: Path,
    output_file: Path,
    extractor_file: Path = DEFAULT_EXTRACTOR_FILE,
    build_target: str = DEFAULT_BUILD_TARGET,
    depth: int = 1,
) -> dict[str, Any]:
    if depth <= 0:
        raise ValueError("depth must be positive")
    if not derived_file.exists():
        raise ValueError(f"Derived file not found: {derived_file}")
    if not extractor_file.exists():
        raise ValueError(f"Dependency extractor file not found: {extractor_file}")

    declaration_names = [decl["name"] for decl in parse_declaration_order(derived_file.read_text(encoding="utf-8"))]
    build_result = subprocess.run(
        ["lake", "build", build_target],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    if build_result.returncode != 0:
        raise RuntimeError(
            "failed to build Derived before dependency extraction: "
            + "\n".join(part for part in (build_result.stdout, build_result.stderr) if part).strip()
        )

    output_file.parent.mkdir(parents=True, exist_ok=True)
    extractor_source = extractor_file.read_text(encoding="utf-8")

    with tempfile.TemporaryDirectory(prefix="derived.deps.") as tmp_dir:
        tmp_path = Path(tmp_dir)
        harness_file = tmp_path / "DerivedDependencyHarness.lean"
        temp_output_file = tmp_path / "derived-deps.json"
        harness_file.write_text(
            _build_harness_source(
                derived_import=build_target,
                extractor_source=extractor_source,
                declaration_names=declaration_names,
                output_file=temp_output_file,
                depth=depth,
            ),
            encoding="utf-8",
        )
        run_result = subprocess.run(
            ["lake", "env", "lean", str(harness_file)],
            cwd=str(REPO_ROOT),
            check=False,
            capture_output=True,
            text=True,
        )
        if run_result.returncode != 0:
            raise RuntimeError(
                "dependency extractor harness failed: "
                + "\n".join(part for part in (run_result.stdout, run_result.stderr) if part).strip()
            )
        if not temp_output_file.exists():
            raise RuntimeError("dependency extractor harness did not produce output JSON")
        payload = json.loads(temp_output_file.read_text(encoding="utf-8"))
        rows = _normalize_dependency_payload(payload, declaration_names=declaration_names, output_file=output_file)
    return {
        "status": "ok",
        "derived_file": str(derived_file),
        "output_file": str(output_file),
        "row_count": len(rows),
        "depth": depth,
        "build_target": build_target,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Extract Derived.lean declaration dependencies via DependencyExtractor.lean")
    parser.add_argument("--derived-file", default=str(DEFAULT_DERIVED_FILE))
    parser.add_argument("--output-file", default=str(DEFAULT_DEPS_FILE))
    parser.add_argument("--extractor-file", default=str(DEFAULT_EXTRACTOR_FILE))
    parser.add_argument("--build-target", default=DEFAULT_BUILD_TARGET)
    parser.add_argument("--depth", type=int, default=1)
    args = parser.parse_args()

    report = extract_derived_dependencies(
        derived_file=Path(args.derived_file),
        output_file=Path(args.output_file),
        extractor_file=Path(args.extractor_file),
        build_target=args.build_target,
        depth=args.depth,
    )
    print(json.dumps(report, ensure_ascii=False))


if __name__ == "__main__":
    main()
