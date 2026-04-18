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
SYNC_GENERATOR_VERSION = 2
GENERATED_FILE_ORDER = (
    "00_index.md",
    "02_section_map.md",
    "03_source_links.md",
)
REPORT_SUFFIXES = {".md", ".markdown"}
IGNORED_REPORT_STEMS = {"00_index", "02_section_map", "03_source_links"}
SECTION_HEADING_RE = re.compile(r"^\s*##+\s*(.+?)\s*$")
URL_LINE_RE = re.compile(r"https?://")
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


def _is_reference_heading(heading: str) -> bool:
    lowered = heading.lower()
    return lowered.startswith(("works cited", "references", "bibliography"))


def _is_auxiliary_heading(heading: str) -> bool:
    lowered = heading.lower()
    return (
        lowered.startswith("table ")
        or lowered.startswith("figure ")
        or lowered.startswith("appendix")
        or _is_reference_heading(heading)
    )


def _extract_section_map_targets(sections: list[str]) -> list[str]:
    targets: list[str] = []
    for heading in sections:
        if _is_auxiliary_heading(heading):
            continue
        targets.append(heading)
    return targets


def _section_usage_line(heading: str) -> str:
    lowered = heading.lower()
    if any(token in lowered for token in ("introduction", "overview", "background", "preliminar", "setup")):
        return "Use for scope, terminology, baseline assumptions, and setup."
    if any(token in lowered for token in ("related work", "literature", "comparison", "prior work")):
        return "Use for closest-known-result checks and literature positioning."
    if any(token in lowered for token in ("method", "approach", "construction", "framework", "technique")):
        return "Use for candidate ideas tied to the report's methods, constructions, or reusable framework."
    if any(token in lowered for token in ("result", "finding", "analysis", "discussion", "case study", "application")):
        return "Use for candidate ideas tied to the report's main claims, examples, or analyses."
    if any(token in lowered for token in ("conclusion", "future", "direction", "open problem", "objective", "agenda")):
        return "Use for significance checks, next-step framing, and candidate selection pressure."
    return "Use for candidate ideas tied to this section's central topic, claims, or vocabulary."


def _extract_works_cited_lines(text: str) -> list[str]:
    lines = text.splitlines()
    in_works_cited = False
    source_lines: list[str] = []
    for raw_line in lines:
        stripped = raw_line.strip()
        normalized = _strip_markdown_emphasis(stripped).lower()
        if _is_reference_heading(normalized):
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
        "  Section-to-task map for problem generation and problem evaluation.\n"
        "- `03_source_links.md`\n"
        "  Reference list extracted from the report for direct paper access.\n"
        "\n"
        "## Usage\n\n"
        "- Problem generation:\n"
        "  Read `02_section_map.md` first. Use the main report when a section needs more context.\n"
        "- Problem evaluation:\n"
        "  Read `02_section_map.md` first. Use the main report when deciding whether a candidate is central, duplicative, or merely local.\n"
    )


def _render_section_map(section_targets: list[str]) -> str:
    blocks = ["# Section Map\n", "\n", "## Problem Generation\n", "\n"]
    for heading in section_targets:
        blocks.append(f"- `{heading}`\n")
        blocks.append(f"  {_section_usage_line(heading)}\n")
    blocks.extend(
        [
            "\n## Problem Evaluation\n\n",
            "- Prefer candidates that align with the report's main themes, scope, and stated research pressure.\n",
            "- Down-rank candidates that only tweak one local example, derivation path, or implementation detail without changing the report-level picture.\n",
            "- Use the report to distinguish broad contribution vs. local continuation, central claim vs. side observation, and real extension vs. rediscovery.\n",
        ]
    )
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
        needs_refresh = (
            previous.get("content_hash") != content_hash
            or int(previous.get("generator_version", 0) or 0) != SYNC_GENERATOR_VERSION
            or not existing_outputs
        )

        report_title = _extract_report_title(text, fallback=report_path.stem.replace("_", " "))
        sections = _extract_top_sections(text)
        section_targets = _extract_section_map_targets(sections)
        source_lines = _extract_works_cited_lines(text)

        target_dir.mkdir(parents=True, exist_ok=True)
        generated_files = {
            "00_index.md": _render_index(report_path, report_title, slug),
            "02_section_map.md": _render_section_map(section_targets),
            "03_source_links.md": _render_source_links(report_path, source_lines),
        }
        obsolete_generated_files = ("04_problem_seeds.md",)
        if needs_refresh:
            for filename, body in generated_files.items():
                (target_dir / filename).write_text(body, encoding="utf-8")
        for filename in obsolete_generated_files:
            obsolete_path = target_dir / filename
            if obsolete_path.exists():
                obsolete_path.unlink()

        state[rel_report_path] = {
            "content_hash": content_hash,
            "generator_version": SYNC_GENERATOR_VERSION,
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
