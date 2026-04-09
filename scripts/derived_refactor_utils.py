from __future__ import annotations

import hashlib
import json
import sys
import time
from pathlib import Path
from typing import Any

from append_derived import build_derived_entries_from_file
from common import append_jsonl
from common import write_json_atomic
from prompt_loader import load_prompt_file
from worker_client import WorkerSettings
from worker_client import load_task_worker_settings
from worker_client import load_worker_settings


def debug_log(message: str) -> None:
    timestamp = time.strftime("%H:%M:%S")
    print(f"[{timestamp}] {message}", file=sys.stderr, flush=True)


def emit_progress_event(log_file: Path | None, **fields: Any) -> None:
    event: dict[str, Any] = {"ts": time.strftime("%Y-%m-%dT%H:%M:%S%z")}
    ordered_keys = (
        "pass_name",
        "phase",
        "round",
        "repair_round",
        "result",
        "item_id",
        "stop_reason",
        "error_excerpt",
        "focus_theorem_names",
        "touched_theorems",
    )
    for key in ordered_keys:
        if key not in fields:
            continue
        value = fields.get(key)
        if value in (None, "", []):
            continue
        if key in {"error_excerpt", "stop_reason"}:
            event[key] = single_line_excerpt(str(value), limit=120)
            continue
        if key in {"focus_theorem_names", "touched_theorems"} and isinstance(value, list):
            cleaned = [single_line_excerpt(str(item), limit=60) for item in value if str(item).strip()]
            if not cleaned:
                continue
            event[key] = cleaned[:3]
            if len(cleaned) > 3:
                event[f"{key}_count"] = len(cleaned)
            continue
        event[key] = value

    for key, value in fields.items():
        if key in ordered_keys or value in (None, "", []):
            continue
        if isinstance(value, str):
            event[key] = single_line_excerpt(value, limit=120)
        else:
            event[key] = value
    if log_file is not None:
        append_jsonl(log_file, event)


def emit_progress_start(
    log_file: Path | None,
    *,
    pass_name: str,
    round: int = 0,
    item_id: str = "",
    repair_round: int | None = None,
    focus_theorem_names: list[str] | None = None,
    touched_theorems: list[str] | None = None,
) -> None:
    emit_progress_event(
        log_file,
        pass_name=pass_name,
        phase="start",
        round=round,
        repair_round=repair_round,
        result="running",
        item_id=item_id,
        focus_theorem_names=focus_theorem_names or [],
        touched_theorems=touched_theorems or [],
    )


def emit_progress_finish(
    log_file: Path | None,
    *,
    pass_name: str,
    round: int,
    result: str,
    stop_reason: str = "",
    item_id: str = "",
    repair_round: int | None = None,
    focus_theorem_names: list[str] | None = None,
    touched_theorems: list[str] | None = None,
    error_excerpt: str = "",
) -> None:
    excerpt = error_excerpt or stop_reason
    emit_progress_event(
        log_file,
        pass_name=pass_name,
        phase="finish",
        round=round,
        repair_round=repair_round,
        result=result,
        item_id=item_id,
        stop_reason=stop_reason,
        error_excerpt=excerpt,
        focus_theorem_names=focus_theorem_names or [],
        touched_theorems=touched_theorems or [],
    )


def emit_progress_error(
    log_file: Path | None,
    *,
    pass_name: str,
    phase: str,
    round: int,
    stop_reason: str,
    item_id: str = "",
    repair_round: int | None = None,
    focus_theorem_names: list[str] | None = None,
    touched_theorems: list[str] | None = None,
    error_excerpt: str = "",
) -> None:
    emit_progress_event(
        log_file,
        pass_name=pass_name,
        phase=phase,
        round=round,
        repair_round=repair_round,
        result="error",
        item_id=item_id,
        stop_reason=stop_reason,
        error_excerpt=error_excerpt or stop_reason,
        focus_theorem_names=focus_theorem_names or [],
        touched_theorems=touched_theorems or [],
    )


def build_report(
    status: str,
    stop_reason: str,
    *,
    stop_detail: str = "",
    input_file: Path | str | None = None,
    output_file: Path | str | None = None,
    report_file: Path | str | None = None,
    extra: dict[str, Any] | None = None,
) -> dict[str, Any]:
    report: dict[str, Any] = {
        "status": str(status).strip(),
        "stop_reason": str(stop_reason).strip(),
        "stop_detail": str(stop_detail or "").strip(),
    }
    if input_file is not None:
        report["input_file"] = str(input_file)
    if output_file is not None:
        report["output_file"] = str(output_file)
    if report_file is not None:
        report["report_file"] = str(report_file)
    if extra:
        for key, value in extra.items():
            if value is None:
                continue
            report[key] = value
    return report


def write_report(report_file: Path | None, report: dict[str, Any]) -> None:
    if report_file is None:
        return
    write_json_atomic(report_file, report)


def print_report(report: dict[str, Any]) -> None:
    print(json.dumps(report, ensure_ascii=False))


def load_text(path: Path) -> str:
    if not path.exists():
        raise ValueError(f"File not found: {path}")
    return path.read_text(encoding="utf-8")


def load_prompt_text(path: Path) -> str:
    return load_prompt_file(path)


def single_line_excerpt(text: str, limit: int = 240) -> str:
    normalized = " ".join(text.strip().split())
    if not normalized:
        return ""
    if len(normalized) <= limit:
        return normalized
    return normalized[: limit - 3] + "..."


def normalize_statement_text(statement: str) -> str:
    return " ".join(statement.split())


def candidate_fingerprint(text: str) -> str:
    return hashlib.sha1(text.strip().encode("utf-8")).hexdigest()


def error_fingerprint(text: str) -> str:
    return single_line_excerpt(text).lower()


def build_exact_duplicate_statement_groups(entries: list[dict[str, str]]) -> list[dict[str, Any]]:
    grouped: dict[str, list[str]] = {}
    for entry in entries:
        theorem_name = str(entry.get("theorem_name", "")).strip()
        statement = normalize_statement_text(str(entry.get("statement", "")))
        if not theorem_name or not statement:
            continue
        grouped.setdefault(statement, []).append(theorem_name)

    duplicates: list[dict[str, Any]] = []
    for statement, theorem_names in grouped.items():
        if len(theorem_names) < 2:
            continue
        duplicates.append(
            {
                "statement": statement,
                "theorem_names": theorem_names,
            }
        )
    duplicates.sort(key=lambda item: (len(item["theorem_names"]), item["statement"]), reverse=True)
    return duplicates


def validate_full_file_refactor_output(
    payload: dict[str, Any],
    *,
    label: str,
) -> tuple[str, str, str, list[str], list[str]]:
    required_keys = {"result", "refactored_code", "summary", "change_notes", "touched_theorems"}
    if set(payload.keys()) != required_keys:
        raise ValueError(
            f"{label} must contain exactly: result, refactored_code, summary, change_notes, touched_theorems"
        )

    result = payload.get("result")
    if result not in {"ok", "noop", "stuck"}:
        raise ValueError(f"{label} result must be one of: ok, noop, stuck")

    refactored_code = payload.get("refactored_code")
    summary = payload.get("summary")
    change_notes = payload.get("change_notes")
    touched_theorems = payload.get("touched_theorems")
    if (
        not isinstance(refactored_code, str)
        or not isinstance(summary, str)
        or not isinstance(change_notes, list)
        or not isinstance(touched_theorems, list)
    ):
        raise ValueError(f"{label} fields have invalid types")
    if any(not isinstance(item, str) for item in change_notes):
        raise ValueError("change_notes must contain only strings")
    if any(not isinstance(item, str) for item in touched_theorems):
        raise ValueError("touched_theorems must contain only strings")

    cleaned_code = refactored_code.strip()
    if result == "stuck":
        if cleaned_code:
            raise ValueError("refactored_code must be empty when result=stuck")
    else:
        if not cleaned_code:
            raise ValueError("refactored_code must be non-empty when result is ok or noop")
        if "namespace AutomatedTheoryConstruction" not in cleaned_code:
            raise ValueError("refactored_code must contain namespace AutomatedTheoryConstruction")
        if "end AutomatedTheoryConstruction" not in cleaned_code:
            raise ValueError("refactored_code must end the AutomatedTheoryConstruction namespace")

    cleaned_touched = [item.strip() for item in touched_theorems if item.strip()]
    return (
        str(result),
        cleaned_code,
        summary.strip(),
        [item.strip() for item in change_notes if item.strip()],
        cleaned_touched,
    )


def extract_theorem_entries_from_code(derived_file: Path, code: str) -> list[dict[str, str]]:
    import tempfile

    with tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        suffix=".lean",
        prefix="Derived.refactor.entries.",
        dir=str(derived_file.parent),
        delete=False,
    ) as handle:
        temp_path = Path(handle.name)
        handle.write(code + "\n")

    try:
        return build_derived_entries_from_file(temp_path)
    finally:
        temp_path.unlink(missing_ok=True)


def verify_lean_file(file_path: Path, timeout_sec: int | None) -> dict[str, Any]:
    import subprocess

    cmd = ["lake", "env", "lean", str(file_path)]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout_sec, check=False)
    except subprocess.TimeoutExpired as exc:
        stderr_text = (exc.stderr or "") if isinstance(exc.stderr, str) else ""
        stdout_text = (exc.stdout or "") if isinstance(exc.stdout, str) else ""
        timeout_label = f"{timeout_sec}s" if timeout_sec is not None else "without a limit"
        return {
            "success": False,
            "stderr": f"Lean verification timed out after {timeout_label}\n{stderr_text}".strip(),
            "stdout": stdout_text,
        }

    return {
        "success": proc.returncode == 0,
        "stderr": proc.stderr,
        "stdout": proc.stdout,
    }


def verify_refactored_code(derived_file: Path, code: str, timeout_sec: int | None) -> dict[str, Any]:
    import tempfile

    with tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        suffix=".lean",
        prefix="Derived.refactor.",
        dir=str(derived_file.parent),
        delete=False,
    ) as handle:
        temp_path = Path(handle.name)
        handle.write(code + "\n")

    try:
        result = verify_lean_file(temp_path, timeout_sec=timeout_sec)
        result["checked_file"] = str(temp_path)
        return result
    finally:
        temp_path.unlink(missing_ok=True)


def resolve_refactor_worker_settings(
    *,
    worker_settings: WorkerSettings | None,
    worker_command: str | None,
    worker_timeout: int | None,
) -> WorkerSettings:
    if worker_settings is not None:
        return worker_settings

    base_worker_settings = load_worker_settings(
        command_override=worker_command,
        timeout_override=worker_timeout,
        default_timeout_sec=None,
    )
    refactor_base_settings = WorkerSettings(
        command=base_worker_settings.command,
        timeout_sec=None,
        propagate_timeout=False,
        codex_timeout_sec=base_worker_settings.codex_timeout_sec,
        propagate_codex_timeout=base_worker_settings.propagate_codex_timeout,
    )
    return load_task_worker_settings(
        task_name="refactor_derived",
        base_settings=refactor_base_settings,
        timeout_override=worker_timeout,
    )


def theorem_statement_map(entries: list[dict[str, str]]) -> dict[str, str]:
    return {
        str(entry.get("theorem_name", "")).strip(): normalize_statement_text(str(entry.get("statement", "")))
        for entry in entries
        if str(entry.get("theorem_name", "")).strip()
    }


def compare_theorem_inventories(
    before_entries: list[dict[str, str]],
    after_entries: list[dict[str, str]],
) -> dict[str, Any]:
    before_map = theorem_statement_map(before_entries)
    after_map = theorem_statement_map(after_entries)
    missing_names = sorted(name for name in before_map if name not in after_map)
    changed_statements = sorted(name for name, stmt in before_map.items() if after_map.get(name) not in {None, stmt})
    return {
        "ok": not missing_names and not changed_statements,
        "missing_names": missing_names,
        "changed_statements": changed_statements,
        "before_theorem_count": len(before_entries),
        "after_theorem_count": len(after_entries),
    }


def check_order_preservation_outside_region(
    before_entries: list[dict[str, str]],
    after_entries: list[dict[str, str]],
    allowed_region: list[str],
) -> dict[str, Any]:
    allowed = {name.strip() for name in allowed_region if name.strip()}
    before_names = [str(entry.get("theorem_name", "")).strip() for entry in before_entries]
    after_names = [str(entry.get("theorem_name", "")).strip() for entry in after_entries]
    before_outside = [name for name in before_names if name and name not in allowed]
    after_outside = [name for name in after_names if name and name not in allowed]
    return {
        "ok": before_outside == after_outside,
        "before_outside": before_outside,
        "after_outside": after_outside,
    }


def detect_no_progress(history: list[dict[str, Any]], *, window: int = 4) -> tuple[bool, str]:
    if len(history) < window:
        return False, ""

    recent = history[-window:]
    recent_results = [str(item.get("result", "")).strip() for item in recent]
    recent_candidate_hashes = [str(item.get("candidate_hash", "")).strip() for item in recent]
    recent_errors = [str(item.get("error_fingerprint", "")).strip() for item in recent]

    if all(result == "noop" for result in recent_results):
        return True, "repeated_noop"

    if len(set(hash_value for hash_value in recent_candidate_hashes if hash_value)) == 1:
        nonempty_errors = [error for error in recent_errors if error]
        if nonempty_errors and len(set(nonempty_errors)) == 1:
            return True, "same_candidate_same_error"

    failing_results = {"verify_failed", "policy_failed"}
    if all(result in failing_results for result in recent_results):
        nonempty_errors = [error for error in recent_errors if error]
        if nonempty_errors and len(set(nonempty_errors)) == 1:
            return True, "repeated_failure_same_error"

    return False, ""


def normalize_stop_reason(raw_reason: str) -> tuple[str, str]:
    reason = str(raw_reason or "").strip()
    if not reason:
        return "completed", ""
    if reason.startswith("budget_exhausted:"):
        return "budget_exhausted", reason.split(":", 1)[1].strip()
    if reason == "max_wall_clock_reached":
        return "budget_exhausted", "max_wall_clock_reached"
    if reason.startswith("no_progress:"):
        return "no_progress", reason.split(":", 1)[1].strip()
    if reason.startswith("worker_error:"):
        return "worker_error", reason.split(":", 1)[1].strip()
    if reason in {
        "budget_exhausted",
        "same_error_streak",
        "no_progress",
        "worker_stuck",
        "worker_timeout",
        "worker_error",
        "verify_failed",
        "policy_failed",
        "no_candidates",
        "completed",
    }:
        return reason, ""
    return reason, ""
