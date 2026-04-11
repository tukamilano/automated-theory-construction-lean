from __future__ import annotations

import json
import os
import re
import tempfile
from pathlib import Path
from typing import Any


ID_PATTERN = re.compile(r"^op_(\d+)$")
OPEN_PROBLEM_PRIORITY_LABELS = {"high", "medium", "low", "unknown"}
ARCHIVED_PROBLEMS_FILENAME = "archived_problems.jsonl"
LEGACY_DEFERRED_PROBLEMS_FILENAME = "deferred_problems.jsonl"
LEGACY_PRUNED_OPEN_PROBLEMS_FILENAME = "pruned_open_problems.jsonl"
LEAN_IMPORT_PATTERN = re.compile(r"^\s*import\s+([A-Za-z0-9_.']+)\s*$", re.MULTILINE)


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        rows.append(json.loads(line))
    return rows


def write_jsonl_atomic(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = "".join(json.dumps(row, ensure_ascii=False, separators=(",", ":")) + "\n" for row in rows)
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=str(path.parent), delete=False) as tmp:
        tmp.write(payload)
        tmp_path = Path(tmp.name)
    os.replace(tmp_path, path)


def append_jsonl(path: Path, row: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(row, ensure_ascii=False, separators=(",", ":")) + "\n")


def write_json_atomic(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    serialized = json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=str(path.parent), delete=False) as tmp:
        tmp.write(serialized)
        tmp_path = Path(tmp.name)
    os.replace(tmp_path, path)


def normalize_stmt(stmt: str) -> str:
    return " ".join(stmt.strip().lower().split())


def parse_problem_index(problem_id: str) -> int | None:
    match = ID_PATTERN.match(problem_id)
    if not match:
        return None
    return int(match.group(1))


def next_problem_id(all_ids: list[str]) -> str:
    max_index = 0
    for problem_id in all_ids:
        idx = parse_problem_index(problem_id)
        if idx is not None and idx > max_index:
            max_index = idx
    return f"op_{max_index + 1:06d}"


def _coerce_nonnegative_int(value: Any, default: int) -> int:
    try:
        parsed = int(value)
    except (TypeError, ValueError):
        return default
    return parsed if parsed >= 0 else default


def normalize_open_problem_priority(value: Any) -> str:
    raw = str(value or "").strip().lower()
    if raw in OPEN_PROBLEM_PRIORITY_LABELS:
        return raw
    try:
        parsed = int(raw)
    except (TypeError, ValueError):
        return "unknown"
    if parsed >= 3:
        return "high"
    if parsed == 2:
        return "medium"
    if parsed == 1:
        return "low"
    return "unknown"


def normalize_open_problem_row(row: dict[str, Any]) -> dict[str, Any]:
    normalized = dict(row)
    normalized.pop("n", None)

    src = str(normalized.get("src", "generated") or "generated").strip() or "generated"
    normalized["src"] = src
    normalized["mode"] = str(normalized.get("mode", "local_support") or "local_support").strip() or "local_support"
    normalized["summary_delta"] = str(normalized.get("summary_delta", "") or "").strip()
    # Legacy metadata fields are intentionally dropped from the normalized row.
    normalized.pop("bottleneck_hit", None)
    normalized.pop("agenda_alignment", None)
    normalized.pop("why_not_peripheral", None)
    normalized.pop("unlocks", None)
    parent_problem_ids = normalized.get("parent_problem_ids", [])
    if isinstance(parent_problem_ids, list):
        normalized["parent_problem_ids"] = [str(item).strip() for item in parent_problem_ids if str(item).strip()]
    else:
        normalized["parent_problem_ids"] = []
    normalized["priority"] = normalize_open_problem_priority(normalized.get("priority"))
    normalized["priority_rationale"] = str(normalized.get("priority_rationale", "") or "").strip()
    normalized["failure_count"] = _coerce_nonnegative_int(normalized.get("failure_count"), 0)
    normalized.pop("priority_refreshed_at_theorem_count", None)
    normalized.pop("attempt_count", None)
    normalized.pop("last_attempt_iteration", None)
    normalized.pop("last_result", None)
    normalized.pop("pruned_at_iteration", None)
    normalized.pop("pruned_reason", None)
    return normalized


def dedupe_problem_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    deduped: list[dict[str, Any]] = []
    seen_ids: set[str] = set()
    for row in rows:
        normalized = normalize_open_problem_row(row)
        problem_id = str(normalized.get("id", "")).strip()
        if not problem_id or problem_id in seen_ids:
            continue
        seen_ids.add(problem_id)
        deduped.append(normalized)
    return deduped


def dedupe_problem_rows_by_stmt(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    deduped: list[dict[str, Any]] = []
    seen_ids: set[str] = set()
    seen_stmt_norms: set[str] = set()
    for row in rows:
        normalized = normalize_open_problem_row(row)
        problem_id = str(normalized.get("id", "")).strip()
        if not problem_id or problem_id in seen_ids:
            continue
        stmt_norm = normalize_stmt(str(normalized.get("stmt", "")))
        if stmt_norm and stmt_norm in seen_stmt_norms:
            continue
        seen_ids.add(problem_id)
        if stmt_norm:
            seen_stmt_norms.add(stmt_norm)
        deduped.append(normalized)
    return deduped


def merge_archived_problem_rows(
    existing_rows: list[dict[str, Any]],
    new_rows: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    merged_rows: list[dict[str, Any]] = []
    seen_ids: set[str] = set()
    for row in existing_rows + new_rows:
        normalized = normalize_open_problem_row(row)
        problem_id = str(normalized.get("id", "")).strip()
        if not problem_id or problem_id in seen_ids:
            continue
        seen_ids.add(problem_id)
        merged_rows.append(normalized)
    return merged_rows


def read_archived_problem_rows(data_dir: Path) -> list[dict[str, Any]]:
    paths = [
        data_dir / ARCHIVED_PROBLEMS_FILENAME,
        data_dir / LEGACY_DEFERRED_PROBLEMS_FILENAME,
        data_dir / LEGACY_PRUNED_OPEN_PROBLEMS_FILENAME,
    ]
    combined_rows: list[dict[str, Any]] = []
    for path in paths:
        combined_rows.extend(read_jsonl(path))
    return dedupe_problem_rows(combined_rows)


def is_active_open_problem(row: dict[str, Any], *, failure_threshold: int) -> bool:
    normalized = normalize_open_problem_row(row)
    if normalize_open_problem_priority(normalized.get("priority")) == "low":
        return False
    failure_count = int(normalized.get("failure_count", 0) or 0)
    if failure_threshold > 0 and failure_count >= failure_threshold:
        return False
    return True


def partition_open_problem_rows(
    rows: list[dict[str, Any]],
    *,
    failure_threshold: int,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    active_rows: list[dict[str, Any]] = []
    archived_rows: list[dict[str, Any]] = []
    for row in rows:
        normalized = normalize_open_problem_row(row)
        if is_active_open_problem(normalized, failure_threshold=failure_threshold):
            active_rows.append(normalized)
        else:
            archived_rows.append(normalized)
    return active_rows, archived_rows


def _default_repo_root() -> Path:
    return Path(__file__).resolve().parent.parent


def _resolve_repo_local_module_path(module_name: str, repo_root: Path) -> Path | None:
    module_parts = [part for part in module_name.strip().split(".") if part]
    if not module_parts:
        return None
    candidate = repo_root.joinpath(*module_parts).with_suffix(".lean")
    if candidate.exists():
        return candidate.resolve()
    return None


def _iter_repo_local_import_paths(file_path: Path, repo_root: Path) -> list[Path]:
    try:
        content = file_path.read_text(encoding="utf-8")
    except OSError:
        return []

    import_paths: list[Path] = []
    seen_paths: set[Path] = set()
    for match in LEAN_IMPORT_PATTERN.finditer(content):
        resolved = _resolve_repo_local_module_path(match.group(1), repo_root)
        if resolved is None or resolved == file_path.resolve() or resolved in seen_paths:
            continue
        seen_paths.add(resolved)
        import_paths.append(resolved)
    return import_paths


def collect_repo_local_lean_context_files(
    entry_file: Path,
    *,
    repo_root: Path | None = None,
) -> list[Path]:
    resolved_entry = entry_file.resolve()
    if not resolved_entry.exists():
        return []

    resolved_repo_root = (repo_root or _default_repo_root()).resolve()
    ordered_files: list[Path] = []
    visited: set[Path] = set()
    visiting: set[Path] = set()

    def visit(file_path: Path) -> None:
        resolved = file_path.resolve()
        if resolved in visited or resolved in visiting:
            return
        visiting.add(resolved)
        ordered_files.append(resolved)
        for imported in _iter_repo_local_import_paths(resolved, resolved_repo_root):
            visit(imported)
        visiting.remove(resolved)
        visited.add(resolved)

    visit(resolved_entry)

    # `Theory.lean` is the Lean import boundary used by Derived/Scratch, but for
    # prompt-facing context we also want nearby Lambek developments that are not
    # imported directly because some aggregate imports currently trigger notation
    # ambiguities or heavy rebuild failures in Lean.
    theory_path = (resolved_repo_root / "AutomatedTheoryConstruction" / "Theory.lean").resolve()
    if resolved_entry == theory_path:
        lambek_files = sorted(
            {
                path.resolve()
                for path in (resolved_repo_root / "AutomatedTheoryConstruction").glob("Lambek*.lean")
            }
            | {
                path.resolve()
                for path in (resolved_repo_root / "AutomatedTheoryConstruction" / "Lambek").rglob("*.lean")
            }
        )
        for path in lambek_files:
            if path not in visited and path not in visiting:
                ordered_files.append(path)
                visited.add(path)
    return ordered_files


def render_lean_context(files: list[Path], *, repo_root: Path | None = None) -> str:
    if not files:
        return ""

    resolved_repo_root = (repo_root or _default_repo_root()).resolve()
    blocks: list[str] = []
    for file_path in files:
        resolved = file_path.resolve()
        try:
            display_path = resolved.relative_to(resolved_repo_root)
        except ValueError:
            display_path = resolved
        blocks.append(
            f"-- FILE: {display_path}\n{resolved.read_text(encoding='utf-8').rstrip()}"
        )
    return "\n\n".join(blocks).strip()


def load_theory_context(
    theory_file: Path,
    *,
    repo_root: Path | None = None,
) -> tuple[list[Path], str]:
    files = collect_repo_local_lean_context_files(theory_file, repo_root=repo_root)
    return files, render_lean_context(files, repo_root=repo_root)
