from __future__ import annotations

import argparse
import shutil
import sys
import threading
import time
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
SCRIPTS_ROOT = SCRIPT_DIR.parent
scripts_root_str = str(SCRIPTS_ROOT)
if scripts_root_str not in sys.path:
    sys.path.insert(0, scripts_root_str)

from derived_refactor_utils import build_report
from derived_refactor_utils import compare_theorem_inventories
from derived_refactor_utils import debug_log
from derived_refactor_utils import extract_theorem_entries_from_code
from derived_refactor_utils import print_report
from derived_refactor_utils import repair_theorem_headers_from_source
from derived_refactor_utils import write_report
from llm_exec import build_exec_command
from llm_exec import resolve_provider
from llm_exec import run_llm_exec


DEFAULT_INPUT = Path("AutomatedTheoryConstruction/Derived.refactored.preview.lean")
DEFAULT_OUTPUT = Path("AutomatedTheoryConstruction/Derived.refactored.reviewed.lean")
DEFAULT_REPORT = Path("AutomatedTheoryConstruction/Derived.refactored.reviewed.report.json")
DEFAULT_POLICY = Path(".codex/skills/lean-review-refactor-policy/SKILL.md")
DEFAULT_LEAN_RULE = Path(".codex/skills/lean-rule/SKILL.md")
DEFAULT_MATHLIB_USAGE = Path(".codex/skills/mathlib-usage/SKILL.md")
HEARTBEAT_INTERVAL_SEC = 10.0


def _tail_excerpt(text: str, *, max_lines: int = 8, max_chars: int = 800) -> list[str]:
    lines = [line.rstrip() for line in text.splitlines() if line.strip()]
    if not lines:
        return []
    excerpt = lines[-max_lines:]
    joined = "\n".join(excerpt)
    if len(joined) <= max_chars:
        return excerpt
    trimmed = joined[-max_chars:]
    trimmed_lines = [line for line in trimmed.splitlines() if line.strip()]
    return trimmed_lines or excerpt[-1:]


def _file_observation(path: Path) -> dict[str, Any]:
    observed: dict[str, Any] = {"path": str(path), "exists": path.exists()}
    if not path.exists():
        return observed
    stat = path.stat()
    observed["size_bytes"] = stat.st_size
    observed["mtime_epoch_sec"] = stat.st_mtime
    return observed


def _write_running_report(
    report_file: Path,
    *,
    input_file: Path,
    output_file: Path,
    provider: str,
    model: str | None,
    sandbox: str,
    verify_requested: bool,
    skip_copy: bool,
    phase: str,
    elapsed_sec: float,
    extra: dict[str, Any] | None = None,
) -> None:
    write_report(
        report_file,
        build_report(
            "running",
            phase,
            input_file=input_file,
            output_file=output_file,
            report_file=report_file,
            extra={
                "provider": provider,
                "model": model or "",
                "sandbox": sandbox,
                "verify_requested": verify_requested,
                "skip_copy": skip_copy,
                "elapsed_sec": round(elapsed_sec, 1),
                "output_observation": _file_observation(output_file),
                **(extra or {}),
            },
        ),
    )


def build_prompt(
    *,
    input_file: Path,
    output_file: Path,
    verify: bool,
    verify_command: str | None,
    task_label: str,
    extra_instruction: str,
    policy_file: Path,
    lean_rule_file: Path,
    mathlib_usage_file: Path,
) -> str:
    verify_target = verify_command.strip() if verify_command else f"lake env lean {output_file}"
    verify_step = f"- Run `{verify_target}` after each meaningful edit and fix any resulting errors.\n" if verify else ""
    final_step = f"- Before finishing, run `{verify_target}` and ensure it succeeds.\n" if verify else ""
    extra_step = (extra_instruction.strip() + "\n") if extra_instruction.strip() else ""
    return f"""Use these repository-local guidance files while you work:
- {policy_file}
- {lean_rule_file}
- {mathlib_usage_file}

Task:
- {task_label} `{output_file}` as a non-semantic refactor.
- `{output_file}` was copied from `{input_file}` and should be edited in place.
- Preserve all public theorem names, theorem statements, namespace structure, and intended API.
- Do not redesign the theorem inventory.
- Prefer review-focused cleanup only: localize `classical`, remove brittle proof steps, tidy `have` structure, remove `by exact`, and prefer stable rewrites / `simpa` / short `calc` blocks.
- For paper-claim-style results, prefer rewriting proofs to explicitly reuse existing `Derived.lean` theorems when that can be done without changing statements.
- Do not introduce `sorry`.
- Do not add or remove global instances, `[simp]` attributes, notation, coercions, or transparency changes.
{extra_step}{verify_step}{final_step}
When finished, give a short summary of the non-semantic cleanup you made and whether the final Lean check passed.
"""
def main() -> int:
    parser = argparse.ArgumentParser(
        description="Thin wrapper around the configured LLM CLI for review-polishing Derived Lean files."
    )
    parser.add_argument("--input-file", default=str(DEFAULT_INPUT))
    parser.add_argument("--output-file", default=str(DEFAULT_OUTPUT))
    parser.add_argument("--report-file", default=str(DEFAULT_REPORT))
    parser.add_argument("--provider")
    parser.add_argument("--model")
    parser.add_argument("--sandbox", default="workspace-write")
    parser.add_argument("--skip-copy", action="store_true")
    parser.add_argument("--no-verify", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--print-worker-output", action="store_true")
    parser.add_argument("--verify-command")
    parser.add_argument("--task-label", default="Review-polish")
    parser.add_argument("--extra-instruction", default="")
    parser.add_argument("--policy-file", default=str(DEFAULT_POLICY))
    parser.add_argument("--lean-rule-file", default=str(DEFAULT_LEAN_RULE))
    parser.add_argument("--mathlib-usage-file", default=str(DEFAULT_MATHLIB_USAGE))
    args = parser.parse_args()

    input_file = Path(args.input_file)
    output_file = Path(args.output_file)
    report_file = Path(args.report_file)
    provider = resolve_provider(args.provider)
    policy_file = Path(args.policy_file)
    lean_rule_file = Path(args.lean_rule_file)
    mathlib_usage_file = Path(args.mathlib_usage_file)
    before_entries = extract_theorem_entries_from_code(input_file, input_file.read_text(encoding="utf-8")) if input_file.exists() else []

    if not input_file.exists():
        report = build_report(
            "error",
            "input_missing",
            stop_detail=f"input file not found: {input_file}",
            input_file=input_file,
            output_file=output_file,
            report_file=report_file,
        )
        write_report(report_file, report)
        print_report(report)
        return 1
    for path in (policy_file, lean_rule_file, mathlib_usage_file):
        if not path.exists():
            report = build_report(
                "error",
                "guidance_missing",
                stop_detail=f"guidance file not found: {path}",
                input_file=input_file,
                output_file=output_file,
                report_file=report_file,
            )
            write_report(report_file, report)
            print_report(report)
            return 1

    output_file.parent.mkdir(parents=True, exist_ok=True)
    if not args.skip_copy:
        shutil.copyfile(input_file, output_file)
    debug_log(
        "Review pass setup complete: "
        f"input={input_file} output={output_file} copied={'no' if args.skip_copy else 'yes'}"
    )
    started_monotonic = time.monotonic()
    _write_running_report(
        report_file,
        input_file=input_file,
        output_file=output_file,
        provider=provider,
        model=args.model,
        sandbox=args.sandbox,
        verify_requested=not args.no_verify,
        skip_copy=bool(args.skip_copy),
        phase="worker_pending",
        elapsed_sec=0.0,
        extra={"before_theorem_count": len(before_entries)},
    )

    prompt = build_prompt(
        input_file=input_file,
        output_file=output_file,
        verify=not args.no_verify,
        verify_command=args.verify_command,
        task_label=args.task_label,
        extra_instruction=args.extra_instruction,
        policy_file=policy_file,
        lean_rule_file=lean_rule_file,
        mathlib_usage_file=mathlib_usage_file,
    )

    cmd = build_exec_command(
        provider=provider,
        sandbox=args.sandbox,
        model=args.model,
    )

    if args.dry_run:
        report = build_report(
            "noop",
            "dry_run",
            stop_detail="dry-run requested",
            input_file=input_file,
            output_file=output_file,
            report_file=report_file,
            extra={
                "provider": provider,
                "model": args.model or "",
                "sandbox": args.sandbox,
                "verify_requested": not args.no_verify,
                "skip_copy": bool(args.skip_copy),
                "command": cmd,
            },
        )
        write_report(report_file, report)
        print_report(report)
        return 0

    stop_heartbeat = threading.Event()

    def _heartbeat() -> None:
        last_signature: tuple[bool, int | None, float | None] | None = None
        while not stop_heartbeat.wait(HEARTBEAT_INTERVAL_SEC):
            observation = _file_observation(output_file)
            signature = (
                bool(observation.get("exists")),
                int(observation.get("size_bytes")) if observation.get("size_bytes") is not None else None,
                float(observation.get("mtime_epoch_sec")) if observation.get("mtime_epoch_sec") is not None else None,
            )
            elapsed = time.monotonic() - started_monotonic
            if signature != last_signature:
                debug_log(
                    "Review pass heartbeat: "
                    f"elapsed={elapsed:.1f}s size={observation.get('size_bytes', 0)}"
                )
                last_signature = signature
            _write_running_report(
                report_file,
                input_file=input_file,
                output_file=output_file,
                provider=provider,
                model=args.model,
                sandbox=args.sandbox,
                verify_requested=not args.no_verify,
                skip_copy=bool(args.skip_copy),
                phase="worker_running",
                elapsed_sec=elapsed,
                extra={"before_theorem_count": len(before_entries)},
            )

    heartbeat_thread = threading.Thread(target=_heartbeat, name="review-heartbeat", daemon=True)
    heartbeat_thread.start()

    try:
        completed = run_llm_exec(
            provider=provider,
            prompt=prompt,
            sandbox=args.sandbox,
            model=args.model,
            capture_output=True,
        )
    except Exception as exc:
        stop_heartbeat.set()
        heartbeat_thread.join(timeout=1.0)
        report = build_report(
            "error",
            "worker_error",
            stop_detail=str(exc),
            input_file=input_file,
            output_file=output_file,
            report_file=report_file,
            extra={
                "provider": provider,
                "model": args.model or "",
                "sandbox": args.sandbox,
                "verify_requested": not args.no_verify,
                "skip_copy": bool(args.skip_copy),
            },
        )
        write_report(report_file, report)
        print_report(report)
        return 1
    stop_heartbeat.set()
    heartbeat_thread.join(timeout=1.0)

    if args.print_worker_output:
        if completed.stdout:
            sys.stdout.write(completed.stdout)
            sys.stdout.flush()
        if completed.stderr:
            sys.stderr.write(completed.stderr)
            sys.stderr.flush()

    stop_reason = "completed" if completed.returncode == 0 else "worker_error"
    stdout_excerpt = _tail_excerpt(completed.stdout or "")
    stderr_excerpt = _tail_excerpt(completed.stderr or "")
    if completed.returncode != 0:
        excerpt_lines = stderr_excerpt or stdout_excerpt
        if excerpt_lines:
            sys.stderr.write("[review] worker excerpt:\n")
            sys.stderr.write("\n".join(excerpt_lines) + "\n")
            sys.stderr.flush()
    extra = {
        "provider": provider,
        "model": args.model or "",
        "sandbox": args.sandbox,
        "verify_requested": not args.no_verify,
        "skip_copy": bool(args.skip_copy),
        "returncode": completed.returncode,
        "elapsed_sec": round(time.monotonic() - started_monotonic, 1),
    }
    if completed.returncode == 0:
        try:
            refactored_code = output_file.read_text(encoding="utf-8")
        except Exception as exc:
            stop_reason = "output_read_failed"
            extra["output_read_error"] = str(exc)
        else:
            after_entries = extract_theorem_entries_from_code(output_file, refactored_code)
            inventory_check = compare_theorem_inventories(before_entries, after_entries)
            extra["before_theorem_count"] = inventory_check["before_theorem_count"]
            extra["after_theorem_count"] = inventory_check["after_theorem_count"]
            if not inventory_check["ok"]:
                extra["missing_names"] = inventory_check["missing_names"]
                extra["changed_statements"] = inventory_check["changed_statements"]
                if inventory_check["changed_statements"] and not inventory_check["missing_names"]:
                    repaired_code, repaired_names = repair_theorem_headers_from_source(
                        input_file.read_text(encoding="utf-8"),
                        refactored_code,
                        inventory_check["changed_statements"],
                    )
                    extra["inventory_repair_attempted"] = True
                    extra["inventory_repair_replaced_headers"] = repaired_names
                    if repaired_names:
                        output_file.write_text(repaired_code, encoding="utf-8")
                        repaired_entries = extract_theorem_entries_from_code(output_file, repaired_code)
                        inventory_check = compare_theorem_inventories(before_entries, repaired_entries)
                        extra["before_theorem_count"] = inventory_check["before_theorem_count"]
                        extra["after_theorem_count"] = inventory_check["after_theorem_count"]
                        extra["missing_names"] = inventory_check["missing_names"]
                        extra["changed_statements"] = inventory_check["changed_statements"]
                if not inventory_check["ok"]:
                    stop_reason = "inventory_changed"
    else:
        extra["stdout_excerpt"] = stdout_excerpt
        extra["stderr_excerpt"] = stderr_excerpt
    status = "ok" if stop_reason == "completed" else "error"
    stop_detail = ""
    if stop_reason == "worker_error":
        stop_detail = f"review command exited with code {completed.returncode}"
    elif stop_reason == "output_read_failed":
        stop_detail = f"review output could not be read: {extra.get('output_read_error', '')}"
    elif stop_reason == "inventory_changed":
        stop_detail = (
            "review output changed theorem inventory: "
            f"missing={len(extra.get('missing_names', []))}, "
            f"changed_statements={len(extra.get('changed_statements', []))}"
        )
    report = build_report(
        status,
        stop_reason,
        stop_detail=stop_detail,
        input_file=input_file,
        output_file=output_file,
        report_file=report_file,
        extra=extra,
    )
    write_report(report_file, report)
    print_report(report)
    return 0 if status == "ok" else 1


if __name__ == "__main__":
    raise SystemExit(main())
