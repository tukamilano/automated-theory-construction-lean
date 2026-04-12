from __future__ import annotations

import argparse
import json
import ssl
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
from urllib.request import Request
from urllib.request import urlopen

from materials import DEFAULT_MATERIALS_DIR
from materials import load_materials
from materials_pipeline import DOWNLOADS_DIRNAME
from materials_pipeline import build_source_id
from materials_pipeline import choose_download_filename
from materials_pipeline import default_materials_cache_dir
from materials_pipeline import load_download_index
from materials_pipeline import parse_source_link_entries
from materials_pipeline import save_download_index


USER_AGENT = "ATC-materials-fetch/0.1"


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def _download(url: str, *, timeout_sec: int, ssl_insecure: bool) -> tuple[bytes, str]:
    request = Request(url, headers={"User-Agent": USER_AGENT})
    context = ssl._create_unverified_context() if ssl_insecure else None
    with urlopen(request, timeout=timeout_sec, context=context) as response:
        return response.read(), response.headers.get_content_type() or ""


def fetch_material_sources(
    *,
    materials_dir: Path,
    cache_dir: Path,
    limit: int | None,
    refresh: bool,
    timeout_sec: int,
    ssl_insecure: bool,
) -> dict[str, Any]:
    materials = load_materials(materials_dir)
    source_link_entries = materials.get("source_link_entries", [])
    if not isinstance(source_link_entries, list):
        source_link_entries = parse_source_link_entries(materials.get("source_links", []))

    downloads_dir = cache_dir / DOWNLOADS_DIRNAME
    downloads_dir.mkdir(parents=True, exist_ok=True)
    existing_index = load_download_index(cache_dir)
    by_source_id = {str(item.get("source_id", "")).strip(): dict(item) for item in existing_index}

    fetched: list[dict[str, Any]] = []
    attempted = 0
    for entry in source_link_entries:
        if not isinstance(entry, dict):
            continue
        label = str(entry.get("label", "")).strip()
        url = str(entry.get("url", "")).strip()
        if not label or not url:
            continue
        if limit is not None and attempted >= limit:
            break
        attempted += 1

        source_id = build_source_id(label=label, url=url)
        previous = by_source_id.get(source_id, {})
        previous_relpath = str(previous.get("local_relpath", "")).strip()
        previous_path = cache_dir / previous_relpath if previous_relpath else None
        if not refresh and previous_path is not None and previous_path.exists():
            fetched.append(dict(previous, status="cached"))
            continue

        blob, content_type = _download(url, timeout_sec=timeout_sec, ssl_insecure=ssl_insecure)
        filename = choose_download_filename(label=label, url=url, content_type=content_type)
        output_path = downloads_dir / filename
        output_path.write_bytes(blob)
        record = {
            "source_id": source_id,
            "label": label,
            "url": url,
            "content_type": content_type,
            "local_relpath": str(output_path.relative_to(cache_dir)),
            "fetched_at": _utc_now_iso(),
        }
        by_source_id[source_id] = record
        fetched.append(dict(record, status="downloaded"))

    ordered_records = [by_source_id[key] for key in sorted(by_source_id.keys())]
    save_download_index(cache_dir, ordered_records)
    return {
        "materials_dir": str(materials_dir.resolve()),
        "cache_dir": str(cache_dir.resolve()),
        "attempted": attempted,
        "entries": fetched,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Download source-link materials into a local cache.")
    parser.add_argument("--materials-dir", default=str(DEFAULT_MATERIALS_DIR))
    parser.add_argument("--cache-dir")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--refresh", action="store_true")
    parser.add_argument("--timeout-sec", type=int, default=30)
    parser.add_argument("--ssl-insecure", action="store_true")
    args = parser.parse_args()

    materials_dir = Path(args.materials_dir)
    cache_dir = Path(args.cache_dir) if args.cache_dir else default_materials_cache_dir(materials_dir)
    report = fetch_material_sources(
        materials_dir=materials_dir,
        cache_dir=cache_dir,
        limit=args.limit,
        refresh=args.refresh,
        timeout_sec=args.timeout_sec,
        ssl_insecure=args.ssl_insecure,
    )
    print(json.dumps(report, ensure_ascii=False))


if __name__ == "__main__":
    main()
