from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
SCRIPTS_ROOT = SCRIPT_DIR.parent
scripts_root_str = str(SCRIPTS_ROOT)
if scripts_root_str not in sys.path:
    sys.path.insert(0, scripts_root_str)

from append_derived import build_derived_entries_from_file


REPO_ROOT = SCRIPTS_ROOT.parent
DEFAULT_EXTRACTOR_FILE = REPO_ROOT / "LeanTools/TheoremTypeAlphaGroups.lean"
DEFAULT_NAMESPACE_PREFIX = "AutomatedTheoryConstruction"
DEFAULT_EQUIVALENCE_MODE = "defeq"
EQUIVALENCE_MODES = {"alpha", "defeq"}


def _lean_string_literal(text: str) -> str:
    return json.dumps(text)


def _lean_name_literal(full_name: str) -> str:
    return f"`{full_name}"


def _qualify_decl_name(theorem_name: str, namespace_prefix: str = DEFAULT_NAMESPACE_PREFIX) -> str:
    cleaned = theorem_name.strip()
    if not cleaned or "." in cleaned:
        return cleaned
    return f"{namespace_prefix}.{cleaned}"


def _module_name_from_file(input_file: Path) -> str:
    resolved = input_file.resolve()
    try:
        relative = resolved.relative_to(REPO_ROOT)
    except ValueError as exc:
        raise ValueError(f"input file must be inside repo root: {input_file}") from exc
    if relative.suffix != ".lean":
        raise ValueError(f"input file must be a .lean file: {input_file}")
    return ".".join(relative.with_suffix("").parts)


def _build_harness_source(
    *,
    target_import: str,
    extractor_source: str,
    declaration_names: list[str],
    output_file: Path,
    duplicate_function_name: str,
) -> str:
    names_block = "\n".join(f"  {_lean_name_literal(name)}," for name in declaration_names)
    return (
        f"import {target_import}\n\n"
        f"{extractor_source.rstrip()}\n\n"
        "def targetDecls : List Name := [\n"
        f"{names_block}\n"
        "]\n\n"
        "#eval do\n"
        f"  let groups <- {duplicate_function_name} targetDecls\n"
        "  let js := theoremTypeClustersToJson groups\n"
        f"  let _ <- writeJsonToFile {_lean_string_literal(str(output_file))} js\n"
    )


def _duplicate_function_name(equivalence_mode: str) -> str:
    if equivalence_mode == "alpha":
        return "duplicateTheoremTypeClusters"
    if equivalence_mode == "defeq":
        return "duplicateTheoremTypeClustersDefEq"
    raise ValueError(f"unsupported equivalence mode: {equivalence_mode}")


def _normalize_payload(payload: Any) -> list[dict[str, Any]]:
    if not isinstance(payload, list):
        raise ValueError("alpha-group extractor did not return a JSON list")
    normalized: list[dict[str, Any]] = []
    for row in payload:
        if not isinstance(row, dict):
            raise ValueError("alpha-group row must be an object")
        representative_name = str(row.get("representative_name", "")).strip()
        statement = str(row.get("statement", "")).strip()
        theorem_names = [str(item).strip() for item in row.get("theorem_names", []) if str(item).strip()]
        if not representative_name:
            raise ValueError("alpha-group row is missing representative_name")
        if not statement:
            raise ValueError("alpha-group row is missing statement")
        if len(theorem_names) < 2:
            raise ValueError("alpha-group row must contain at least two theorem_names")
        normalized.append(
            {
                "representative_name": representative_name,
                "statement": statement,
                "theorem_names": theorem_names,
            }
        )
    return normalized


def extract_theorem_type_alpha_groups(
    *,
    input_file: Path,
    output_file: Path,
    extractor_file: Path = DEFAULT_EXTRACTOR_FILE,
    build_target: str | None = None,
    equivalence_mode: str = DEFAULT_EQUIVALENCE_MODE,
) -> dict[str, Any]:
    if not input_file.exists():
        raise ValueError(f"input file not found: {input_file}")
    if not extractor_file.exists():
        raise ValueError(f"extractor file not found: {extractor_file}")
    if equivalence_mode not in EQUIVALENCE_MODES:
        raise ValueError(f"unsupported equivalence mode: {equivalence_mode}")

    declaration_names = [
        _qualify_decl_name(str(entry.get("theorem_name", "")).strip())
        for entry in build_derived_entries_from_file(input_file)
        if str(entry.get("theorem_name", "")).strip()
    ]
    if not declaration_names:
        output_file.parent.mkdir(parents=True, exist_ok=True)
        output_file.write_text("[]\n", encoding="utf-8")
        return {
            "status": "ok",
            "input_file": str(input_file),
            "output_file": str(output_file),
            "group_count": 0,
            "build_target": build_target or _module_name_from_file(input_file),
            "equivalence_mode": equivalence_mode,
        }

    target_import = build_target or _module_name_from_file(input_file)
    build_result = subprocess.run(
        ["lake", "build", target_import],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    if build_result.returncode != 0:
        raise RuntimeError(
            "failed to build target before alpha-group extraction: "
            + "\n".join(part for part in (build_result.stdout, build_result.stderr) if part).strip()
        )

    output_file.parent.mkdir(parents=True, exist_ok=True)
    extractor_source = extractor_file.read_text(encoding="utf-8")

    with tempfile.TemporaryDirectory(prefix="theorem.type.alpha.") as tmp_dir:
        tmp_path = Path(tmp_dir)
        harness_file = tmp_path / "TheoremTypeAlphaHarness.lean"
        temp_output_file = tmp_path / "theorem-type-alpha-groups.json"
        harness_file.write_text(
            _build_harness_source(
                target_import=target_import,
                extractor_source=extractor_source,
                declaration_names=declaration_names,
                output_file=temp_output_file,
                duplicate_function_name=_duplicate_function_name(equivalence_mode),
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
                "alpha-group extractor harness failed: "
                + "\n".join(part for part in (run_result.stdout, run_result.stderr) if part).strip()
            )
        if not temp_output_file.exists():
            raise RuntimeError("alpha-group extractor harness did not produce output JSON")
        payload = json.loads(temp_output_file.read_text(encoding="utf-8"))
        rows = _normalize_payload(payload)
        output_file.write_text(json.dumps(rows, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    return {
        "status": "ok",
        "input_file": str(input_file),
        "output_file": str(output_file),
        "group_count": len(rows),
        "build_target": target_import,
        "equivalence_mode": equivalence_mode,
    }


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Extract theorem groups whose elaborated types are equivalent under the selected mode."
    )
    parser.add_argument("--input-file", required=True)
    parser.add_argument("--output-file", required=True)
    parser.add_argument("--extractor-file", default=str(DEFAULT_EXTRACTOR_FILE))
    parser.add_argument("--build-target")
    parser.add_argument("--equivalence-mode", choices=sorted(EQUIVALENCE_MODES), default=DEFAULT_EQUIVALENCE_MODE)
    args = parser.parse_args()

    report = extract_theorem_type_alpha_groups(
        input_file=Path(args.input_file),
        output_file=Path(args.output_file),
        extractor_file=Path(args.extractor_file),
        build_target=args.build_target,
        equivalence_mode=str(args.equivalence_mode),
    )
    print(json.dumps(report, ensure_ascii=False))


if __name__ == "__main__":
    main()
