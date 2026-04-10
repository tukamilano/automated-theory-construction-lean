from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any

from extract_derived_dependencies import extract_derived_dependencies
from generated_library import DEFAULT_GENERATED_CATALOG
from generated_library import DEFAULT_GENERATED_MANIFEST
from generated_library import DEFAULT_GENERATED_ROOT
from generated_library import ensure_generated_scaffold
from generated_library import render_generated_chunk
from generated_library import write_generated_catalog
from generated_library import write_generated_manifest
from plan_derived_chunks import DEFAULT_DEPS_FILE
from plan_derived_chunks import build_chunk_plan
from refactor_pass_runner import run_refactor_pass
from refactor_pass_specs import EXACT_DUPLICATE_PASS_SPEC
from refactor_pass_specs import PROOF_RETARGET_PASS_SPEC


DERIVED_TEMPLATE = (
    "import Mathlib\n"
    "import AutomatedTheoryConstruction.Theory\n\n"
    "set_option autoImplicit false\n\n"
    "namespace AutomatedTheoryConstruction\n\n"
    "open Mathling.Lambek.ProductFree\n"
    "open scoped Mathling.Lambek.ProductFree\n\n"
    "-- Verified theorems are appended here by scripts/append_derived.py.\n"
    "-- Keep any short theorem docstrings/comments here instead of a separate metadata index.\n\n"
    "end AutomatedTheoryConstruction\n"
)

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_DERIVED_FILE = Path("AutomatedTheoryConstruction/Derived.lean")
DEFAULT_PLAN_FILE = Path("data/derived-chunk-plan.json")
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


def _short_text(value: Any, limit: int = 160) -> str:
    text = " ".join(str(value).split())
    return text if len(text) <= limit else text[: limit - 3] + "..."


def _emit_pass_action_logs(*, chunk_file: Path, pass_name: str, report: dict[str, Any]) -> None:
    planner_reports = report.get("planner_reports", [])
    if isinstance(planner_reports, list):
        for index, planner_report in enumerate(planner_reports, start=1):
            if not isinstance(planner_report, dict):
                continue
            summary = _short_text(planner_report.get("summary", ""))
            item_count = int(planner_report.get("item_count", 0) or 0)
            if summary or item_count:
                _print_progress(
                    "chunk_pass_plan",
                    chunk=chunk_file.name,
                    pass_name=pass_name,
                    cycle=index,
                    item_count=item_count,
                    summary=summary,
                )

    executor_reports = report.get("executor_reports", [])
    if isinstance(executor_reports, list):
        for cycle_index, executor_report in enumerate(executor_reports, start=1):
            if not isinstance(executor_report, dict):
                continue
            items = executor_report.get("items", [])
            if not isinstance(items, list):
                continue
            for item in items:
                if not isinstance(item, dict):
                    continue
                touched = item.get("touched_theorems", [])
                touched_label = ",".join(str(name) for name in touched[:3]) if isinstance(touched, list) else ""
                _print_progress(
                    "chunk_pass_action",
                    chunk=chunk_file.name,
                    pass_name=pass_name,
                    cycle=cycle_index,
                    kind=item.get("kind", ""),
                    result=item.get("result", ""),
                    touched=touched_label,
                    summary=_short_text(item.get("summary", "")),
                    notes=_short_text("; ".join(item.get("change_notes", [])) if isinstance(item.get("change_notes"), list) else ""),
                )


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


def _artifact_dir_for(deps_file: Path) -> Path:
    return deps_file.parent / "generated_refactor"


def _resolve_generated_pass_budget(explicit_budget: int | None) -> int | None:
    if explicit_budget not in (None, 0):
        return explicit_budget
    for env_name in (
        "ATC_REFACTOR_DERIVED_CODEX_TIMEOUT",
        "ATC_CODEX_TIMEOUT",
        "ATC_REFACTOR_DERIVED_WORKER_TIMEOUT",
        "ATC_WORKER_TIMEOUT",
    ):
        raw = os.environ.get(env_name)
        if raw is None or raw.strip() == "":
            continue
        try:
            value = int(raw)
        except ValueError:
            continue
        if value > 0:
            return value
    return None


def _snapshot_generated_root(generated_root: Path) -> Path:
    snapshot_dir = Path(tempfile.mkdtemp(prefix="generated.snapshot."))
    if generated_root.exists():
        shutil.copytree(generated_root, snapshot_dir / "Generated", dirs_exist_ok=True)
    return snapshot_dir


def _restore_generated_root(snapshot_dir: Path, generated_root: Path) -> None:
    source = snapshot_dir / "Generated"
    if generated_root.exists():
        shutil.rmtree(generated_root)
    shutil.copytree(source, generated_root)


def _cleanup_snapshot(snapshot_dir: Path | None) -> None:
    if snapshot_dir is None:
        return
    shutil.rmtree(snapshot_dir, ignore_errors=True)


def _pass_artifact_paths(artifact_dir: Path, chunk_file: Path, pass_name: str) -> tuple[Path, Path]:
    artifact_dir.mkdir(parents=True, exist_ok=True)
    safe_pass_name = pass_name.replace(".", "_")
    prefix = artifact_dir / f"{chunk_file.stem}.{safe_pass_name}"
    return Path(f"{prefix}.plan.json"), Path(f"{prefix}.report.json")


def _run_chunk_pass(
    *,
    spec: Any,
    chunk_file: Path,
    theory_file: Path,
    theorem_reuse_memory_file: Path,
    artifact_dir: Path,
    verify_timeout_sec: int | None,
    max_wall_clock_sec: int | None,
) -> dict[str, Any]:
    plan_file, report_file = _pass_artifact_paths(artifact_dir, chunk_file, spec.pass_name)
    return run_refactor_pass(
        spec,
        input_file=chunk_file,
        output_file=chunk_file,
        theory_file=theory_file,
        plan_file=plan_file,
        report_file=report_file,
        progress_log_file=None,
        planner_prompt_file=spec.default_planner_prompt,
        executor_prompt_file=spec.default_executor_prompt,
        theorem_reuse_memory_file=theorem_reuse_memory_file,
        verify_timeout=verify_timeout_sec,
        max_wall_clock_sec=max_wall_clock_sec,
        print_final_report=False,
    )


def _repair_generated_after_failure(
    *,
    generated_root: Path,
    manifest_file: Path,
    focus_file: Path,
    artifact_dir: Path,
    diagnostics: str,
    max_rounds: int,
    verify_timeout_sec: int | None,
) -> dict[str, Any]:
    report_file = artifact_dir / f"{focus_file.stem}.generated_repair.report.json"
    verify_command = "lake build AutomatedTheoryConstruction.Generated.Manifest"
    last_detail = diagnostics.strip()
    for round_index in range(1, max_rounds + 1):
        _print_progress(
            "generated_repair_round_start",
            round=round_index,
            focus_file=focus_file.name,
        )
        extra_instruction = (
            "This file belongs to the Generated chunk library.\n"
            "Fix only what is necessary so the full Generated manifest builds again.\n"
            "Preserve theorem names, theorem statements, imports, and namespace structure unless the build error "
            "forces a minimal change.\n"
            f"Current build diagnostics:\n{last_detail[:4000]}"
        )
        cmd = [
            sys.executable,
            str((REPO_ROOT / "scripts" / "direct_refactor_derived.py").resolve()),
            "--input-file",
            str(focus_file),
            "--output-file",
            str(focus_file),
            "--report-file",
            str(report_file),
            "--skip-copy",
            "--verify-command",
            verify_command,
            "--task-label",
            "Repair Generated chunk integration for",
            "--extra-instruction",
            extra_instruction,
        ]
        completed = subprocess.run(cmd, cwd=str(REPO_ROOT), check=False)
        build_result = _run_manifest_build(verify_timeout_sec)
        _print_progress(
            "generated_repair_round_result",
            round=round_index,
            focus_file=focus_file.name,
            worker_status="ok" if completed.returncode == 0 else "error",
            manifest_success=build_result["success"],
        )
        if bool(build_result.get("success", False)):
            return {
                "status": "ok",
                "repair_rounds": round_index,
                "detail": str(build_result.get("detail", "")),
            }
        last_detail = str(build_result.get("detail", "")).strip() or last_detail
    return {
        "status": "error",
        "repair_rounds": max_rounds,
        "detail": last_detail,
    }


def _run_generated_local_refactors(
    *,
    generated_root: Path,
    manifest_file: Path,
    theory_file: Path,
    theorem_reuse_memory_file: Path,
    artifact_dir: Path,
    run_pass_1_2_per_file: bool,
    run_pass_1_3_per_file: bool,
    pass_1_2_max_wall_clock_sec_per_file: int | None,
    pass_1_3_max_wall_clock_sec_per_file: int | None,
    generated_repair_max_rounds: int,
    generated_repair_verify_timeout: int | None,
) -> list[dict[str, Any]]:
    catalog_file = generated_root / "catalog.json"
    payload = json.loads(catalog_file.read_text(encoding="utf-8"))
    chunk_files = [Path(chunk["file"]) for chunk in payload.get("chunks", []) if isinstance(chunk, dict)]
    results: list[dict[str, Any]] = []
    last_changed_chunk: Path | None = None
    pass_1_2_budget = _resolve_generated_pass_budget(pass_1_2_max_wall_clock_sec_per_file)
    pass_1_3_budget = _resolve_generated_pass_budget(pass_1_3_max_wall_clock_sec_per_file)

    for chunk_file in chunk_files:
        _print_progress("chunk_start", chunk=chunk_file.name)

        if run_pass_1_2_per_file:
            snapshot_dir = _snapshot_generated_root(generated_root)
            _print_progress("chunk_pass_start", chunk=chunk_file.name, pass_name="1.2", budget_sec=pass_1_2_budget)
            report = _run_chunk_pass(
                spec=EXACT_DUPLICATE_PASS_SPEC,
                chunk_file=chunk_file,
                theory_file=theory_file,
                theorem_reuse_memory_file=theorem_reuse_memory_file,
                artifact_dir=artifact_dir,
                verify_timeout_sec=generated_repair_verify_timeout,
                max_wall_clock_sec=pass_1_2_budget,
            )
            accepted_cycles = int(report.get("accepted_cycles", 0) or 0)
            status = str(report.get("status", "ok"))
            stop_reason = str(report.get("stop_reason", "completed"))
            _emit_pass_action_logs(chunk_file=chunk_file, pass_name="1.2", report=report)
            if accepted_cycles > 0:
                build_result = _run_manifest_build(generated_repair_verify_timeout)
                if not bool(build_result.get("success", False)):
                    _print_progress("manifest_verify_result", chunk=chunk_file.name, pass_name="1.2", success=False)
                    repair_result = _repair_generated_after_failure(
                        generated_root=generated_root,
                        manifest_file=manifest_file,
                        focus_file=chunk_file,
                        artifact_dir=artifact_dir,
                        diagnostics=str(build_result.get("detail", "")),
                        max_rounds=generated_repair_max_rounds,
                        verify_timeout_sec=generated_repair_verify_timeout,
                    )
                    if repair_result["status"] != "ok":
                        _restore_generated_root(snapshot_dir, generated_root)
                        results.append(
                            {
                                "chunk": chunk_file.name,
                                "pass": "1.2",
                                "status": "rolled_back_after_failed_repair",
                                "detail": str(repair_result.get("detail", "")),
                            }
                        )
                        _print_progress("rollback_applied", chunk=chunk_file.name, pass_name="1.2")
                    else:
                        last_changed_chunk = chunk_file
                        results.append(
                            {
                                "chunk": chunk_file.name,
                                "pass": "1.2",
                                "status": "repaired_after_failure",
                                "accepted_cycles": accepted_cycles,
                            }
                        )
                else:
                    last_changed_chunk = chunk_file
                    results.append(
                        {
                            "chunk": chunk_file.name,
                            "pass": "1.2",
                            "status": status,
                            "accepted_cycles": accepted_cycles,
                            "stop_reason": stop_reason,
                        }
                    )
                    _print_progress(
                        "chunk_pass_result",
                        chunk=chunk_file.name,
                        pass_name="1.2",
                        status=status,
                        accepted_cycles=accepted_cycles,
                    )
            else:
                skip_status = "skipped_no_candidates" if stop_reason == "no_candidates" else status
                results.append({"chunk": chunk_file.name, "pass": "1.2", "status": skip_status, "stop_reason": stop_reason})
                _print_progress("chunk_pass_result", chunk=chunk_file.name, pass_name="1.2", status=skip_status)
            _cleanup_snapshot(snapshot_dir)

        if run_pass_1_3_per_file:
            snapshot_dir = _snapshot_generated_root(generated_root)
            _print_progress("chunk_pass_start", chunk=chunk_file.name, pass_name="1.3", budget_sec=pass_1_3_budget)
            report = _run_chunk_pass(
                spec=PROOF_RETARGET_PASS_SPEC,
                chunk_file=chunk_file,
                theory_file=theory_file,
                theorem_reuse_memory_file=theorem_reuse_memory_file,
                artifact_dir=artifact_dir,
                verify_timeout_sec=generated_repair_verify_timeout,
                max_wall_clock_sec=pass_1_3_budget,
            )
            accepted_cycles = int(report.get("accepted_cycles", 0) or 0)
            status = str(report.get("status", "ok"))
            stop_reason = str(report.get("stop_reason", "completed"))
            _emit_pass_action_logs(chunk_file=chunk_file, pass_name="1.3", report=report)
            if accepted_cycles > 0:
                build_result = _run_manifest_build(generated_repair_verify_timeout)
                if not bool(build_result.get("success", False)):
                    _print_progress("manifest_verify_result", chunk=chunk_file.name, pass_name="1.3", success=False)
                    repair_result = _repair_generated_after_failure(
                        generated_root=generated_root,
                        manifest_file=manifest_file,
                        focus_file=chunk_file,
                        artifact_dir=artifact_dir,
                        diagnostics=str(build_result.get("detail", "")),
                        max_rounds=generated_repair_max_rounds,
                        verify_timeout_sec=generated_repair_verify_timeout,
                    )
                    if repair_result["status"] != "ok":
                        _restore_generated_root(snapshot_dir, generated_root)
                        results.append(
                            {
                                "chunk": chunk_file.name,
                                "pass": "1.3",
                                "status": "rolled_back_after_failed_repair",
                                "detail": str(repair_result.get("detail", "")),
                            }
                        )
                        _print_progress("rollback_applied", chunk=chunk_file.name, pass_name="1.3")
                    else:
                        last_changed_chunk = chunk_file
                        results.append(
                            {
                                "chunk": chunk_file.name,
                                "pass": "1.3",
                                "status": "repaired_after_failure",
                                "accepted_cycles": accepted_cycles,
                            }
                        )
                else:
                    last_changed_chunk = chunk_file
                    results.append(
                        {
                            "chunk": chunk_file.name,
                            "pass": "1.3",
                            "status": status,
                            "accepted_cycles": accepted_cycles,
                            "stop_reason": stop_reason,
                        }
                    )
                    _print_progress(
                        "chunk_pass_result",
                        chunk=chunk_file.name,
                        pass_name="1.3",
                        status=status,
                        accepted_cycles=accepted_cycles,
                    )
            else:
                skip_status = "skipped_no_candidates" if stop_reason == "no_candidates" else status
                results.append({"chunk": chunk_file.name, "pass": "1.3", "status": skip_status, "stop_reason": stop_reason})
                _print_progress("chunk_pass_result", chunk=chunk_file.name, pass_name="1.3", status=skip_status)
            _cleanup_snapshot(snapshot_dir)

    final_build = _run_manifest_build(generated_repair_verify_timeout)
    if not bool(final_build.get("success", False)) and chunk_files:
        focus_file = last_changed_chunk or chunk_files[-1]
        _print_progress("manifest_verify_result", chunk=focus_file.name, pass_name="final", success=False)
        repair_result = _repair_generated_after_failure(
            generated_root=generated_root,
            manifest_file=manifest_file,
            focus_file=focus_file,
            artifact_dir=artifact_dir,
            diagnostics=str(final_build.get("detail", "")),
            max_rounds=generated_repair_max_rounds,
            verify_timeout_sec=generated_repair_verify_timeout,
        )
        results.append(
            {
                "chunk": focus_file.name,
                "pass": "final",
                "status": "repaired_after_failure" if repair_result["status"] == "ok" else "error",
                "detail": str(repair_result.get("detail", "")),
            }
        )
    return results


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
    run_pass_1_2_per_file: bool = False,
    run_pass_1_3_per_file: bool = False,
    pass_1_2_max_wall_clock_sec_per_file: int | None = None,
    pass_1_3_max_wall_clock_sec_per_file: int | None = None,
    generated_repair_max_rounds: int = 2,
    generated_repair_verify_timeout: int | None = 300,
) -> dict[str, Any]:
    generated_root, manifest_file, catalog_file = _resolve_generated_paths(
        derived_file=derived_file,
        generated_root=generated_root,
        manifest_file=manifest_file,
        catalog_file=catalog_file,
    )
    artifact_dir = _artifact_dir_for(deps_file)
    _print_progress(
        "start",
        derived_file=derived_file,
        generated_root=generated_root,
        run_pass_1_2_per_file=run_pass_1_2_per_file,
        run_pass_1_3_per_file=run_pass_1_3_per_file,
    )
    dependency_report: dict[str, Any] | None = None
    if refresh_dependencies:
        dependency_report = extract_derived_dependencies(
            derived_file=derived_file,
            output_file=deps_file,
            depth=deps_depth,
        )
    derived_text = derived_file.read_text(encoding="utf-8")
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

    chunk_passes: list[dict[str, Any]] = []
    if run_pass_1_2_per_file or run_pass_1_3_per_file:
        chunk_passes = _run_generated_local_refactors(
            generated_root=generated_root,
            manifest_file=manifest_file,
            theory_file=theory_file,
            theorem_reuse_memory_file=theorem_reuse_memory_file,
            artifact_dir=artifact_dir,
            run_pass_1_2_per_file=run_pass_1_2_per_file,
            run_pass_1_3_per_file=run_pass_1_3_per_file,
            pass_1_2_max_wall_clock_sec_per_file=pass_1_2_max_wall_clock_sec_per_file,
            pass_1_3_max_wall_clock_sec_per_file=pass_1_3_max_wall_clock_sec_per_file,
            generated_repair_max_rounds=generated_repair_max_rounds,
            generated_repair_verify_timeout=generated_repair_verify_timeout,
        )

    if reset_derived:
        derived_file.write_text(DERIVED_TEMPLATE, encoding="utf-8")

    should_run_final_manifest_build = bool(verify_manifest or run_pass_1_2_per_file or run_pass_1_3_per_file)
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
        "artifact_dir": str(artifact_dir),
        "chunk_count": len(catalog_chunks),
        "chunk_passes": chunk_passes,
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
    parser.add_argument("--theorem-reuse-memory-file", default="data/theorem_reuse_memory.json")
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
    parser.add_argument("--run-pass-1_2-per-file", action=argparse.BooleanOptionalAction, default=False)
    parser.add_argument("--run-pass-1_3-per-file", action=argparse.BooleanOptionalAction, default=False)
    parser.add_argument("--pass-1_2-max-wall-clock-sec-per-file", type=int)
    parser.add_argument("--pass-1_3-max-wall-clock-sec-per-file", type=int)
    parser.add_argument("--generated-repair-max-rounds", type=int, default=2)
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
        run_pass_1_2_per_file=bool(args.run_pass_1_2_per_file),
        run_pass_1_3_per_file=bool(args.run_pass_1_3_per_file),
        pass_1_2_max_wall_clock_sec_per_file=args.pass_1_2_max_wall_clock_sec_per_file,
        pass_1_3_max_wall_clock_sec_per_file=args.pass_1_3_max_wall_clock_sec_per_file,
        generated_repair_max_rounds=args.generated_repair_max_rounds,
        generated_repair_verify_timeout=args.generated_repair_verify_timeout,
    )
    print(json.dumps(report, ensure_ascii=False))


if __name__ == "__main__":
    main()
