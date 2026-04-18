from __future__ import annotations

import argparse
import json
import re
import sys
import tempfile
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
SCRIPTS_ROOT = SCRIPT_DIR.parent
scripts_root_str = str(SCRIPTS_ROOT)
if scripts_root_str not in sys.path:
    sys.path.insert(0, scripts_root_str)

from derived_refactor_utils import build_report
from derived_refactor_utils import print_report
from derived_refactor_utils import write_report
from refactor.extract_theorem_type_alpha_groups import extract_theorem_type_alpha_groups


DECL_PATTERN = re.compile(r"^(theorem|lemma|def|abbrev|inductive|structure)\s+([^\s:({]+)", re.MULTILINE)
END_NAMESPACE_PATTERN = re.compile(r"^end\s+AutomatedTheoryConstruction\s*$", re.MULTILINE)
DEFAULT_NAMESPACE_PREFIX = "AutomatedTheoryConstruction."


def _short_name(name: str) -> str:
    cleaned = str(name).strip()
    if cleaned.startswith(DEFAULT_NAMESPACE_PREFIX):
        return cleaned[len(DEFAULT_NAMESPACE_PREFIX) :]
    return cleaned.rsplit(".", 1)[-1]


def _attached_docstring_start(text: str, decl_start: int) -> int:
    cursor = decl_start
    while cursor > 0 and text[cursor - 1].isspace():
        cursor -= 1
    if not text[:cursor].endswith("-/"):
        return decl_start
    doc_start = text.rfind("/--", 0, cursor)
    if doc_start < 0:
        return decl_start
    return doc_start


def _theorem_block_spans(text: str) -> dict[str, tuple[int, int]]:
    matches = list(DECL_PATTERN.finditer(text))
    end_namespace = END_NAMESPACE_PATTERN.search(text)
    final_end = end_namespace.start() if end_namespace is not None else len(text)
    spans: dict[str, tuple[int, int]] = {}
    for index, match in enumerate(matches):
        kind = str(match.group(1))
        short_name = str(match.group(2)).strip()
        if kind != "theorem" or not short_name:
            continue
        block_start = _attached_docstring_start(text, match.start())
        block_end = final_end
        if index + 1 < len(matches):
            block_end = matches[index + 1].start()
        spans[short_name] = (block_start, block_end)
    return spans


def _remove_spans(text: str, spans: list[tuple[int, int]]) -> str:
    updated = text
    for start, end in sorted(spans, key=lambda span: span[0], reverse=True):
        updated = updated[:start] + updated[end:]
    updated = re.sub(r"\n{3,}", "\n\n", updated)
    return updated


def _load_alpha_groups(
    *,
    alpha_source_file: Path,
    build_target: str,
    equivalence_mode: str,
) -> list[dict[str, Any]]:
    with tempfile.TemporaryDirectory(prefix="alpha-dedupe.") as tmp_dir:
        tmp_output = Path(tmp_dir) / "alpha-groups.json"
        extract_theorem_type_alpha_groups(
            input_file=alpha_source_file,
            output_file=tmp_output,
            build_target=build_target,
            equivalence_mode=equivalence_mode,
        )
        payload = json.loads(tmp_output.read_text(encoding="utf-8"))
    if not isinstance(payload, list):
        raise ValueError("alpha-group extractor returned a non-list payload")
    return [row for row in payload if isinstance(row, dict)]


def delete_alpha_equiv_duplicates(
    *,
    input_file: Path,
    output_file: Path,
    alpha_source_file: Path,
    build_target: str,
    equivalence_mode: str = "defeq",
    report_file: Path | None = None,
) -> dict[str, Any]:
    if not input_file.exists():
        raise ValueError(f"input file not found: {input_file}")
    if not alpha_source_file.exists():
        raise ValueError(f"alpha source file not found: {alpha_source_file}")

    text = input_file.read_text(encoding="utf-8")
    theorem_spans = _theorem_block_spans(text)
    alpha_groups = _load_alpha_groups(
        alpha_source_file=alpha_source_file,
        build_target=build_target,
        equivalence_mode=equivalence_mode,
    )

    removed_theorems: list[str] = []
    kept_theorems: list[str] = []
    spans_to_remove: list[tuple[int, int]] = []

    for group in alpha_groups:
        theorem_names_raw = group.get("theorem_names", [])
        if not isinstance(theorem_names_raw, list):
            continue
        ordered_short_names = [_short_name(name) for name in theorem_names_raw if _short_name(name)]
        present_names = [name for name in ordered_short_names if name in theorem_spans]
        if len(present_names) < 2:
            continue
        kept_theorems.append(present_names[0])
        for duplicate_name in present_names[1:]:
            removed_theorems.append(duplicate_name)
            spans_to_remove.append(theorem_spans[duplicate_name])

    updated_text = _remove_spans(text, spans_to_remove) if spans_to_remove else text
    output_file.parent.mkdir(parents=True, exist_ok=True)
    output_file.write_text(updated_text, encoding="utf-8")

    report = build_report(
        "ok",
        "completed",
        input_file=input_file,
        output_file=output_file,
        report_file=report_file,
        extra={
            "alpha_source_file": str(alpha_source_file),
            "build_target": build_target,
            "equivalence_mode": equivalence_mode,
            "alpha_group_count": len(alpha_groups),
            "removed_theorems": removed_theorems,
            "removed_count": len(removed_theorems),
            "kept_representatives": kept_theorems,
        },
    )
    write_report(report_file, report)
    return report


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Delete later theorem blocks whose theorem types are equivalent to earlier ones under the selected mode."
    )
    parser.add_argument("--input-file", required=True)
    parser.add_argument("--output-file", required=True)
    parser.add_argument("--alpha-source-file", required=True)
    parser.add_argument("--build-target", required=True)
    parser.add_argument("--equivalence-mode", choices=("alpha", "defeq"), default="defeq")
    parser.add_argument("--report-file")
    args = parser.parse_args()

    report = delete_alpha_equiv_duplicates(
        input_file=Path(args.input_file),
        output_file=Path(args.output_file),
        alpha_source_file=Path(args.alpha_source_file),
        build_target=str(args.build_target),
        equivalence_mode=str(args.equivalence_mode),
        report_file=Path(args.report_file) if args.report_file else None,
    )
    print_report(report)


if __name__ == "__main__":
    main()
