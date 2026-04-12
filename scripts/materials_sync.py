from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any

from materials import DEFAULT_MATERIALS_DIR
from materials_extract import extract_material_sources
from materials_fetch import fetch_material_sources
from materials_pipeline import default_materials_cache_dir


SYNC_STATE_FILENAME = ".materials_sync_state.json"
GENERATED_FILE_ORDER = (
    "00_index.md",
    "02_section_map.md",
    "03_source_links.md",
    "04_problem_seeds.md",
)
REPORT_SUFFIXES = {".md", ".markdown"}
IGNORED_REPORT_STEMS = {"00_index", "02_section_map", "03_source_links", "04_problem_seeds"}
SECTION_HEADING_RE = re.compile(r"^\s*##+\s*(.+?)\s*$")
NUMBERED_ITEM_RE = re.compile(r"^\s*\d+\.\s+\*\*(.+?)\*\*:\s*(.*)$")
URL_LINE_RE = re.compile(r"https?://")
NON_ALNUM_RE = re.compile(r"[^a-z0-9]+")

DEFAULT_EVALUATION_CHECKS = (
    "Does this candidate change the summary of the structural theory rather than extend one proof path?",
    "Is it closer to a structural correspondence, a reducibility claim, an invertibility claim, a separability claim, a completeness limit, or a decidability boundary?",
    "Is it merely a cosmetic restatement, an unprincipled proliferation of structural rules, a one-off example, or an unproductive negative statement?",
    "Would solving it help with a canonical target identified by the report rather than only improving one local derivation?",
)
DEFAULT_MAIN_THEOREM_USAGE = (
    "Start from the main report when candidate construction depends on the report's structural summary or future-direction framing.",
    "Read `03_source_links.md` when novelty, closest known result, or literature positioning depends on cited papers rather than only the report summary.",
)


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _strip_markdown_emphasis(text: str) -> str:
    cleaned = str(text).strip()
    cleaned = re.sub(r"[*_`]+", "", cleaned)
    cleaned = re.sub(r"^\d+\.\s*", "", cleaned)
    return " ".join(cleaned.split()).strip()


def _discover_reports(materials_dir: Path) -> list[Path]:
    reports: list[Path] = []
    for path in sorted(item for item in materials_dir.iterdir() if item.is_file() and not item.name.startswith(".")):
        if path.suffix.lower() not in REPORT_SUFFIXES:
            continue
        if path.stem in IGNORED_REPORT_STEMS:
            continue
        reports.append(path)
    return reports


def _load_sync_state(materials_dir: Path) -> dict[str, Any]:
    path = materials_dir / SYNC_STATE_FILENAME
    if not path.exists():
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}
    return payload if isinstance(payload, dict) else {}


def _save_sync_state(materials_dir: Path, state: dict[str, Any]) -> None:
    (materials_dir / SYNC_STATE_FILENAME).write_text(
        json.dumps(state, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


def _derive_slug(report_path: Path) -> str:
    tokens = re.findall(r"[A-Za-z0-9]+", report_path.stem)
    if not tokens:
        return "materials"
    preferred = str(tokens[0]).lower()
    return preferred or "materials"


def _extract_report_title(text: str, fallback: str) -> str:
    for raw_line in text.splitlines():
        stripped = raw_line.strip()
        if stripped.startswith("#"):
            title = _strip_markdown_emphasis(stripped.lstrip("#").strip())
            if title:
                return title
    return fallback


def _extract_top_sections(text: str) -> list[str]:
    sections: list[str] = []
    for raw_line in text.splitlines():
        match = SECTION_HEADING_RE.match(raw_line)
        if not match:
            continue
        heading = _strip_markdown_emphasis(match.group(1))
        lowered = heading.lower()
        if lowered.startswith("table of contents"):
            continue
        sections.append(heading)
    return sections


def _extract_section_map_targets(sections: list[str]) -> list[str]:
    targets: list[str] = []
    for heading in sections:
        lowered = heading.lower()
        if lowered.startswith(("10.", "11.", "12.")):
            break
        targets.append(heading)
    return targets


def _section_usage_line(heading: str) -> str:
    lowered = heading.lower()
    if "hierarchy" in lowered or "substructural landscape" in lowered:
        return "Use for choosing structural-rule regimes and language-side motivation."
    if "correspondence" in lowered or "language hierarch" in lowered:
        return "Use for correspondence-style, expressivity, and grammar-class problems."
    if "complexity" in lowered or "decidability" in lowered:
        return "Use for complexity boundaries, rule-sensitive fragments, and decidability pressure."
    if "provability" in lowered or "reducibility" in lowered or "exchange" in lowered:
        return "Use for reducibility, exchange-modality, and bridge-style problem generation."
    if "invertibility" in lowered or "focusing" in lowered or "proof search" in lowered:
        return "Use for invertibility, focusing, and proof-search structure problems."
    if "separability" in lowered or "separation" in lowered:
        return "Use for separation statements and non-derivability boundaries."
    if "completeness" in lowered or "algebraic" in lowered or "model" in lowered:
        return "Use for completeness, incompleteness, and algebraic-obstruction problems."
    if "syntax-semantics" in lowered or "curry-howard" in lowered or "semantics" in lowered:
        return "Use for structural preservation and syntax-semantics interface problems."
    return "Use when the candidate appears to depend on this report section's theorem family or boundary claim."


def _extract_generation_anchors(text: str, sections: list[str]) -> list[str]:
    candidate_phrases = (
        "provability relations among structural rules",
        "discovery of invertibility",
        "rigorous separation of expressive power",
        "algebraic limits of completeness theorems",
        "sharp boundaries of decidability and cut-elimination",
        "structural preservation properties",
        "structural correspondences",
        "language hierarchies",
        "cut-elimination",
        "decidability frontier",
    )
    lowered = text.lower()
    anchors: list[str] = []
    for phrase in candidate_phrases:
        if phrase in lowered and phrase not in anchors:
            anchors.append(phrase)
    if anchors:
        return anchors[:6]
    fallback: list[str] = []
    for heading in sections:
        cleaned = heading.split(".", 1)[-1].strip() if "." in heading else heading
        lowered_heading = cleaned.lower()
        if lowered_heading in fallback:
            continue
        fallback.append(lowered_heading)
        if len(fallback) >= 6:
            break
    return fallback


def _extract_main_theorem_triggers(text: str) -> list[str]:
    lines = text.splitlines()
    in_targets = False
    triggers: list[str] = []
    for raw_line in lines:
        stripped = raw_line.strip()
        if not stripped:
            continue
        normalized = _strip_markdown_emphasis(stripped).lower()
        if normalized.startswith("10. canonical objectives and future directions") or normalized.startswith("canonical objectives and future directions"):
            in_targets = True
            continue
        if in_targets and stripped.startswith("##"):
            break
        if not in_targets:
            continue
        match = NUMBERED_ITEM_RE.match(stripped)
        if match is None:
            continue
        label = _strip_markdown_emphasis(match.group(1))
        if label and label.lower() not in {item.lower() for item in triggers}:
            triggers.append(label.lower())
    return triggers[:6]


def _extract_works_cited_lines(text: str) -> list[str]:
    lines = text.splitlines()
    in_works_cited = False
    source_lines: list[str] = []
    for raw_line in lines:
        stripped = raw_line.strip()
        normalized = _strip_markdown_emphasis(stripped).lower()
        if normalized.startswith("works cited"):
            in_works_cited = True
            continue
        if in_works_cited and stripped.startswith("##"):
            break
        if not in_works_cited:
            continue
        if URL_LINE_RE.search(stripped):
            source_lines.append(stripped)
    if source_lines:
        return source_lines
    return [line.strip() for line in lines if URL_LINE_RE.search(line)]


def _render_index(report_path: Path, report_title: str, slug: str) -> str:
    return (
        f"# {slug.capitalize()} Materials Index\n\n"
        f"This directory organizes the materials derived from `{report_path.name}` without rewriting the main report.\n\n"
        "## Files\n\n"
        f"- `../{report_path.name}`\n"
        "  The main report. Use this when wording, context, or references matter.\n"
        "- `02_section_map.md`\n"
        "  Section-to-task map for problem generation, problem evaluation, and main theorem work.\n"
        "- `03_source_links.md`\n"
        "  Reference list extracted from the report for direct paper access.\n"
        "- `04_problem_seeds.md`\n"
        "  Short extraction of high-value problem families and evaluation checks.\n\n"
        "## Usage\n\n"
        "- Problem generation:\n"
        "  Read `02_section_map.md` and `04_problem_seeds.md` first. Use the main report when a section needs more context.\n"
        "- Problem evaluation:\n"
        "  Read `02_section_map.md` and `04_problem_seeds.md` first. Use the main report when deciding whether a candidate is central, duplicative, or merely local.\n"
        "- Main theorem session:\n"
        "  Start from the main report and `03_source_links.md` when candidate construction or novelty pressure depends on the literature.\n"
    )


def _render_section_map(section_targets: list[str]) -> str:
    blocks = ["# Section Map\n", "\n", "## Problem Generation\n", "\n"]
    for heading in section_targets:
        blocks.append(f"- `{heading}`\n")
        blocks.append(f"  {_section_usage_line(heading)}\n")
    blocks.extend(
        [
            "\n## Problem Evaluation\n\n",
            "- Prefer candidates that align with the report's structural themes and canonical targets.\n",
            "- Down-rank candidates that do not connect to the report's structural themes and only produce narrow local continuation.\n",
            "- Use the report to distinguish: special case vs. generalization, local lemma vs. structural bridge, and benchmark rediscovery vs. research-facing problem.\n",
            "\n## Main Theorem Deep Access\n\n",
        ]
    )
    for line in DEFAULT_MAIN_THEOREM_USAGE:
        blocks.append(f"- {line}\n")
    return "".join(blocks)


def _render_source_links(report_path: Path, source_lines: list[str]) -> str:
    blocks = [
        "# Source Links\n\n",
        f"The following links are extracted from `../{report_path.name}` without normalizing the wording.\n\n",
    ]
    for index, line in enumerate(source_lines, start=1):
        cleaned = str(line).strip()
        if not cleaned:
            continue
        if re.match(r"^\d+\.\s+", cleaned):
            blocks.append(f"{cleaned}\n")
        else:
            blocks.append(f"{index}. {cleaned}\n")
    return "".join(blocks)


def _render_problem_seeds(generation_anchors: list[str], main_theorem_triggers: list[str]) -> str:
    blocks = [
        "# Problem Seeds\n\n",
        "This file keeps the report's main research pressures close to problem generation and problem evaluation.\n\n",
        "## Generation Anchors\n\n",
    ]
    for item in generation_anchors[:6]:
        blocks.append(f"- {item}\n")
    blocks.append("\n## Evaluation Checks\n\n")
    for item in DEFAULT_EVALUATION_CHECKS:
        blocks.append(f"- {item}\n")
    blocks.append("\n## Main Theorem Triggers\n\n")
    triggers = main_theorem_triggers or ["canonical targets identified by the report"]
    for item in triggers[:6]:
        blocks.append(f"- {item}\n")
    return "".join(blocks)


def ensure_materials_derived_current(materials_dir: Path) -> dict[str, Any]:
    root = Path(materials_dir)
    root.mkdir(parents=True, exist_ok=True)
    state = _load_sync_state(root)
    reports_summary: list[dict[str, Any]] = []

    for report_path in _discover_reports(root):
        text = report_path.read_text(encoding="utf-8")
        content_hash = _sha256_text(text)
        rel_report_path = str(report_path.relative_to(root))
        slug = _derive_slug(report_path)
        target_dir = root / slug
        previous = dict(state.get(rel_report_path, {})) if isinstance(state.get(rel_report_path, {}), dict) else {}
        existing_outputs = all((target_dir / filename).exists() for filename in GENERATED_FILE_ORDER)
        needs_refresh = previous.get("content_hash") != content_hash or not existing_outputs

        report_title = _extract_report_title(text, fallback=report_path.stem.replace("_", " "))
        sections = _extract_top_sections(text)
        section_targets = _extract_section_map_targets(sections)
        source_lines = _extract_works_cited_lines(text)
        generation_anchors = _extract_generation_anchors(text, sections)
        main_theorem_triggers = _extract_main_theorem_triggers(text)

        target_dir.mkdir(parents=True, exist_ok=True)
        generated_files = {
            "00_index.md": _render_index(report_path, report_title, slug),
            "02_section_map.md": _render_section_map(section_targets),
            "03_source_links.md": _render_source_links(report_path, source_lines),
            "04_problem_seeds.md": _render_problem_seeds(generation_anchors, main_theorem_triggers),
        }
        if needs_refresh:
            for filename, body in generated_files.items():
                (target_dir / filename).write_text(body, encoding="utf-8")

        state[rel_report_path] = {
            "content_hash": content_hash,
            "slug": slug,
            "report_title": report_title,
            "generated_dir": str(target_dir.relative_to(root)),
            "generated_files": list(GENERATED_FILE_ORDER),
        }
        reports_summary.append(
            {
                "report": rel_report_path,
                "slug": slug,
                "generated_dir": str(target_dir.relative_to(root)),
                "refreshed": bool(needs_refresh),
                "source_link_count": len(source_lines),
            }
        )

    _save_sync_state(root, state)
    return {
        "materials_dir": str(root.resolve()),
        "reports": reports_summary,
    }


def ensure_materials_cache_current(
    materials_dir: Path,
    *,
    fetch_missing: bool,
    extract_downloads: bool,
    timeout_sec: int = 30,
    ssl_insecure: bool = False,
) -> dict[str, Any]:
    root = Path(materials_dir)
    derived_report = ensure_materials_derived_current(root)
    cache_dir = default_materials_cache_dir(root)
    fetch_report: dict[str, Any] = {
        "materials_dir": str(root.resolve()),
        "cache_dir": str(cache_dir.resolve()),
        "attempted": 0,
        "entries": [],
    }
    extract_report: dict[str, Any] = {
        "cache_dir": str(cache_dir.resolve()),
        "processed": 0,
        "entries": [],
    }
    if fetch_missing:
        fetch_report = fetch_material_sources(
            materials_dir=root,
            cache_dir=cache_dir,
            limit=None,
            refresh=False,
            timeout_sec=timeout_sec,
            ssl_insecure=ssl_insecure,
            match_filters=[],
        )
    if extract_downloads:
        extract_report = extract_material_sources(
            materials_dir=root,
            cache_dir=cache_dir,
            limit=None,
        )
    return {
        "materials_dir": str(root.resolve()),
        "cache_dir": str(cache_dir.resolve()),
        "derived": derived_report,
        "fetch": fetch_report,
        "extract": extract_report,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate derived materials files and optionally refresh the materials cache.")
    parser.add_argument("--materials-dir", default=str(DEFAULT_MATERIALS_DIR))
    parser.add_argument("--cache-dir")
    parser.add_argument("--timeout-sec", type=int, default=30)
    parser.add_argument("--ssl-insecure", action="store_true")
    parser.add_argument("--derive-only", action="store_true")
    args = parser.parse_args()

    materials_dir = Path(args.materials_dir)
    _ = Path(args.cache_dir) if args.cache_dir else default_materials_cache_dir(materials_dir)
    report = ensure_materials_cache_current(
        materials_dir,
        fetch_missing=not args.derive_only,
        extract_downloads=not args.derive_only,
        timeout_sec=args.timeout_sec,
        ssl_insecure=args.ssl_insecure,
    )
    print(json.dumps(report, ensure_ascii=False))


if __name__ == "__main__":
    main()
