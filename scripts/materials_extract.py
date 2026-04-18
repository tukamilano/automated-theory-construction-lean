from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from materials import DEFAULT_MATERIALS_DIR
from materials_pipeline import default_materials_cache_dir
from materials_pipeline import extract_paper_record
from materials_pipeline import load_download_index
from materials_pipeline import save_paper_record


def extract_material_sources(
    *,
    materials_dir: Path,
    cache_dir: Path,
    limit: int | None,
) -> dict[str, Any]:
    _ = materials_dir
    download_entries = load_download_index(cache_dir)
    extracted: list[dict[str, Any]] = []
    processed = 0
    for item in download_entries:
        if limit is not None and processed >= limit:
            break
        source_id = str(item.get("source_id", "")).strip()
        label = str(item.get("label", "")).strip()
        source_url = str(item.get("url", "")).strip()
        content_type = str(item.get("content_type", "")).strip()
        local_relpath = str(item.get("local_relpath", "")).strip()
        if not source_id or not source_url or not local_relpath:
            continue
        download_path = cache_dir / local_relpath
        if not download_path.exists():
            continue
        record = extract_paper_record(
            download_path,
            source_id=source_id,
            source_url=source_url,
            label=label,
            content_type=content_type,
        )
        output_path = save_paper_record(cache_dir, record)
        extracted.append(
            {
                "source_id": source_id,
                "title": str(record.get("title", "")).strip(),
                "extract_confidence": str(record.get("extract_confidence", "")).strip(),
                "paper_relpath": str(output_path.relative_to(cache_dir)),
            }
        )
        processed += 1
    return {
        "cache_dir": str(cache_dir.resolve()),
        "processed": processed,
        "entries": extracted,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Extract text/chunks from cached materials downloads.")
    parser.add_argument("--materials-dir", default=str(DEFAULT_MATERIALS_DIR))
    parser.add_argument("--cache-dir")
    parser.add_argument("--limit", type=int)
    args = parser.parse_args()

    materials_dir = Path(args.materials_dir)
    cache_dir = Path(args.cache_dir) if args.cache_dir else default_materials_cache_dir(materials_dir)
    report = extract_material_sources(materials_dir=materials_dir, cache_dir=cache_dir, limit=args.limit)
    print(json.dumps(report, ensure_ascii=False))


if __name__ == "__main__":
    main()
