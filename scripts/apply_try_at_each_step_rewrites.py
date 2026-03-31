from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any


def debug_log(message: str) -> None:
    timestamp = time.strftime("%H:%M:%S")
    print(f"[{timestamp}] {message}", file=sys.stderr, flush=True)


@dataclass(frozen=True)
class Candidate:
    parent_name: str
    start_line: int
    start_col: int
    old_text: str
    old_to_end_of_branch: str
    raw_suggestion: str
    suggestion: str
    stripped_annotation: str | None
    shortened_steps_count: int
    goal_is_prop: bool
    start_idx: int
    end_idx: int

    @property
    def span_text(self) -> str:
        return self.old_to_end_of_branch or self.old_text

    @property
    def span_length(self) -> int:
        return self.end_idx - self.start_idx


def load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def dump_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def verify_lean_file(file_path: Path, timeout_sec: int | None) -> tuple[bool, str]:
    cmd = ["lake", "env", "lean", str(file_path)]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout_sec, check=False)
    except subprocess.TimeoutExpired as exc:
        stderr_text = (exc.stderr or "") if isinstance(exc.stderr, str) else ""
        stdout_text = (exc.stdout or "") if isinstance(exc.stdout, str) else ""
        timeout_label = f"{timeout_sec}s" if timeout_sec is not None else "without a limit"
        combined = f"Lean verification timed out after {timeout_label}\n{stderr_text}\n{stdout_text}".strip()
        return False, combined
    combined = "\n".join(part for part in (proc.stderr, proc.stdout) if part).strip()
    return proc.returncode == 0, combined


def run_try_at_each_step(
    *,
    input_file: Path,
    tactic: str,
    raw_output_file: Path,
) -> tuple[bool, str]:
    raw_output_file.parent.mkdir(parents=True, exist_ok=True)
    cmd = [
        "lake",
        "env",
        "lean",
        "--run",
        "tryAtEachStep/tryAtEachStep.lean",
        tactic,
        str(input_file),
        "--outfile",
        str(raw_output_file),
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True, check=False)
    combined = "\n".join(part for part in (proc.stderr, proc.stdout) if part).strip()
    return proc.returncode == 0, combined


def extract_try_this_tactic(message: str | None) -> str | None:
    if not message:
        return None
    marker = "Try this:"
    idx = message.find(marker)
    if idx < 0:
        return None
    suggestion = message[idx + len(marker) :].strip()
    if not suggestion:
        return None
    return suggestion


def strip_try_this_annotation(suggestion: str) -> tuple[str, str | None]:
    lines = suggestion.splitlines()
    if not lines:
        return suggestion, None
    first = lines[0]
    stripped = first.lstrip()
    if not stripped.startswith("["):
        return suggestion, None
    closing = stripped.find("]")
    if closing <= 1:
        return suggestion, None
    annotation = stripped[1:closing]
    if not all(ch.isalpha() or ch in {"_", "-"} for ch in annotation):
        return suggestion, None
    remainder = stripped[closing + 1 :].lstrip()
    if not remainder:
        return suggestion, None
    indent = first[: len(first) - len(first.lstrip())]
    normalized = "\n".join([indent + remainder, *lines[1:]])
    return normalized, annotation


def compact_snippet(text: str, limit: int = 160) -> str:
    single_line = " ".join(text.strip().split())
    if len(single_line) <= limit:
        return single_line
    return single_line[: limit - 3] + "..."


def compute_line_offsets(text: str) -> list[int]:
    offsets = [0]
    running = 0
    for line in text.splitlines(keepends=True):
        running += len(line)
        offsets.append(running)
    return offsets


def approximate_offset(line_offsets: list[int], start_line: int, start_col: int) -> int:
    if not line_offsets:
        return 0
    clamped_line = max(1, min(start_line, len(line_offsets)))
    line_start = line_offsets[clamped_line - 1]
    # Lean's pretty-printed columns are close to 0-based; subtracting 1 here is robust enough
    # because we still re-search near the approximate offset below.
    return max(0, line_start + max(start_col - 1, 0))


def locate_span(text: str, *, start_line: int, start_col: int, span_text: str) -> tuple[int, int] | None:
    if not span_text:
        return None
    line_offsets = compute_line_offsets(text)
    approx = approximate_offset(line_offsets, start_line, start_col)

    exact = text.find(span_text, approx)
    if exact >= 0:
        return exact, exact + len(span_text)

    window_start = max(0, approx - 400)
    window_end = min(len(text), approx + max(len(span_text), 400))
    local = text.find(span_text, window_start, window_end)
    if local >= 0:
        return local, local + len(span_text)

    global_matches: list[int] = []
    offset = text.find(span_text)
    while offset >= 0:
        global_matches.append(offset)
        offset = text.find(span_text, offset + 1)
    if not global_matches:
        return None

    best = min(global_matches, key=lambda pos: abs(pos - approx))
    return best, best + len(span_text)


def build_candidates(raw_results: list[dict[str, Any]], source_text: str) -> list[Candidate]:
    candidates: list[Candidate] = []
    for item in raw_results:
        if not isinstance(item, dict):
            continue
        raw_suggestion = extract_try_this_tactic(str(item.get("message") or ""))
        if raw_suggestion is None:
            continue
        suggestion, stripped_annotation = strip_try_this_annotation(raw_suggestion)
        old_text = str(item.get("oldText") or "")
        old_to_end_of_branch = str(item.get("oldToEndOfBranch") or old_text)
        start_line = int(item.get("startLine") or 0)
        start_col = int(item.get("startCol") or 0)
        located = locate_span(
            source_text,
            start_line=start_line,
            start_col=start_col,
            span_text=old_to_end_of_branch or old_text,
        )
        if located is None:
            continue
        start_idx, end_idx = located
        candidates.append(
            Candidate(
                parent_name=str(item.get("parentName") or ""),
                start_line=start_line,
                start_col=start_col,
                old_text=old_text,
                old_to_end_of_branch=old_to_end_of_branch,
                raw_suggestion=raw_suggestion,
                suggestion=suggestion,
                stripped_annotation=stripped_annotation,
                shortened_steps_count=int(item.get("shortenedStepsCount") or 0),
                goal_is_prop=bool(item.get("goalIsProp")),
                start_idx=start_idx,
                end_idx=end_idx,
            )
        )
    return candidates


def select_non_overlapping(candidates: list[Candidate]) -> list[Candidate]:
    selected: list[Candidate] = []
    occupied: list[tuple[int, int]] = []
    ranked = sorted(
        candidates,
        key=lambda candidate: (
            candidate.span_length,
            candidate.shortened_steps_count,
            int(candidate.goal_is_prop),
        ),
        reverse=True,
    )
    for candidate in ranked:
        overlaps = any(not (candidate.end_idx <= start or end <= candidate.start_idx) for start, end in occupied)
        if overlaps:
            continue
        selected.append(candidate)
        occupied.append((candidate.start_idx, candidate.end_idx))
    return sorted(selected, key=lambda candidate: candidate.start_idx, reverse=True)


def indentation_prefix(text: str, start_idx: int) -> str:
    line_start = text.rfind("\n", 0, start_idx)
    line_start = 0 if line_start < 0 else line_start + 1
    return text[line_start:start_idx]


def format_replacement(suggestion: str, prefix: str) -> str:
    lines = [line.rstrip() for line in suggestion.strip().splitlines()]
    if not lines:
        return suggestion.strip()
    if len(lines) == 1:
        return lines[0]
    return "\n".join([lines[0], *[prefix + line for line in lines[1:]]])


def copy_input_if_needed(input_file: Path, output_file: Path) -> None:
    if input_file.resolve() == output_file.resolve():
        return
    output_file.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(input_file, output_file)


def write_backup_if_needed(output_file: Path, backup_file: Path | None) -> None:
    if backup_file is None:
        return
    backup_file.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(output_file, backup_file)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run tryAtEachStep on a Lean file and aggressively apply parseable `Try this:` rewrites."
    )
    parser.add_argument("--input-file", default="AutomatedTheoryConstruction/Derived.refactored.preview.lean")
    parser.add_argument("--output-file")
    parser.add_argument("--raw-output-file", default="AutomatedTheoryConstruction/Derived.tryAtEachStep.json")
    parser.add_argument(
        "--apply-report-file",
        default="AutomatedTheoryConstruction/Derived.tryAtEachStep.apply_report.json",
    )
    parser.add_argument("--tactic", default="with_reducible exact?")
    parser.add_argument("--backup-file")
    parser.add_argument("--verify-timeout", type=int)
    parser.add_argument("--dry-run", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    input_file = Path(args.input_file)
    output_file = Path(args.output_file) if args.output_file else input_file
    raw_output_file = Path(args.raw_output_file)
    apply_report_file = Path(args.apply_report_file)
    backup_file = Path(args.backup_file) if args.backup_file else None

    if not input_file.exists():
        raise SystemExit(f"Input file not found: {input_file}")

    if args.dry_run:
        report = {
            "status": "dry_run",
            "input_file": str(input_file),
            "output_file": str(output_file),
            "raw_output_file": str(raw_output_file),
            "apply_report_file": str(apply_report_file),
            "tactic": args.tactic,
        }
        print(json.dumps(report, ensure_ascii=False))
        return 0

    copy_input_if_needed(input_file, output_file)
    write_backup_if_needed(output_file, backup_file)

    debug_log(
        "Running tryAtEachStep: "
        f"input={output_file} tactic={args.tactic} raw_output={raw_output_file}"
    )
    try_ok, try_log = run_try_at_each_step(
        input_file=output_file,
        tactic=args.tactic,
        raw_output_file=raw_output_file,
    )
    if not try_ok:
        report = {
            "status": "try_at_each_step_failed",
            "input_file": str(input_file),
            "output_file": str(output_file),
            "raw_output_file": str(raw_output_file),
            "apply_report_file": str(apply_report_file),
            "tactic": args.tactic,
            "error": try_log,
        }
        dump_json(apply_report_file, report)
        print(json.dumps(report, ensure_ascii=False))
        return 1

    source_text = output_file.read_text(encoding="utf-8")
    raw_results = load_json(raw_output_file)
    if not isinstance(raw_results, list):
        report = {
            "status": "invalid_try_at_each_step_output",
            "raw_output_file": str(raw_output_file),
        }
        dump_json(apply_report_file, report)
        print(json.dumps(report, ensure_ascii=False))
        return 1

    candidates = build_candidates(raw_results, source_text)
    selected = select_non_overlapping(candidates)
    debug_log(
        f"Loaded tryAtEachStep results: raw={len(raw_results)} parseable={len(candidates)} selected={len(selected)}"
    )

    applied: list[dict[str, Any]] = []
    skipped: list[dict[str, Any]] = []
    failed: list[dict[str, Any]] = []
    current_text = source_text

    for candidate in selected:
        located = locate_span(
            current_text,
            start_line=candidate.start_line,
            start_col=candidate.start_col,
            span_text=candidate.span_text,
        )
        if located is None:
            skipped.append(
                {
                    "parent_name": candidate.parent_name,
                    "start_line": candidate.start_line,
                    "start_col": candidate.start_col,
                    "reason": "span_not_found_after_prior_rewrites",
                }
            )
            continue

        start_idx, end_idx = located
        prefix = indentation_prefix(current_text, start_idx)
        replacement = format_replacement(candidate.suggestion, prefix)
        debug_log(
            "Trying rewrite: "
            f"{candidate.parent_name}:{candidate.start_line}:{candidate.start_col} "
            f"old=`{compact_snippet(candidate.span_text)}` "
            f"raw=`{compact_snippet(candidate.raw_suggestion)}` "
            f"replacement=`{compact_snippet(replacement)}`"
            + (
                f" stripped_annotation={candidate.stripped_annotation}"
                if candidate.stripped_annotation is not None
                else ""
            )
        )
        trial_text = current_text[:start_idx] + replacement + current_text[end_idx:]
        output_file.write_text(trial_text, encoding="utf-8")
        ok, verify_log = verify_lean_file(output_file, timeout_sec=args.verify_timeout)
        if ok:
            debug_log(
                "Accepted rewrite: "
                f"{candidate.parent_name}:{candidate.start_line}:{candidate.start_col}"
            )
            current_text = trial_text
            applied.append(
                {
                    "parent_name": candidate.parent_name,
                    "start_line": candidate.start_line,
                    "start_col": candidate.start_col,
                    "old_text": candidate.old_text,
                    "old_to_end_of_branch": candidate.old_to_end_of_branch,
                    "raw_suggestion": candidate.raw_suggestion,
                    "stripped_annotation": candidate.stripped_annotation,
                    "replacement": replacement,
                    "shortened_steps_count": candidate.shortened_steps_count,
                }
            )
            continue

        output_file.write_text(current_text, encoding="utf-8")
        debug_log(
            "Rejected rewrite after verification failure: "
            f"{candidate.parent_name}:{candidate.start_line}:{candidate.start_col}"
        )
        failed.append(
            {
                "parent_name": candidate.parent_name,
                "start_line": candidate.start_line,
                "start_col": candidate.start_col,
                "old_text": candidate.old_text,
                "old_to_end_of_branch": candidate.old_to_end_of_branch,
                "raw_suggestion": candidate.raw_suggestion,
                "stripped_annotation": candidate.stripped_annotation,
                "replacement": replacement,
                "shortened_steps_count": candidate.shortened_steps_count,
                "verify_log_excerpt": verify_log.splitlines()[:20],
            }
        )

    output_file.write_text(current_text, encoding="utf-8")
    final_ok, final_verify_log = verify_lean_file(output_file, timeout_sec=args.verify_timeout)
    status = "ok" if final_ok else "final_verify_failed"
    report = {
        "status": status,
        "input_file": str(input_file),
        "output_file": str(output_file),
        "raw_output_file": str(raw_output_file),
        "apply_report_file": str(apply_report_file),
        "backup_file": str(backup_file) if backup_file is not None else None,
        "tactic": args.tactic,
        "raw_result_count": len(raw_results),
        "parseable_candidate_count": len(candidates),
        "selected_candidate_count": len(selected),
        "applied_count": len(applied),
        "skipped_count": len(skipped),
        "failed_count": len(failed),
        "applied": applied,
        "skipped": skipped,
        "failed": failed,
        "final_verify_success": final_ok,
        "final_verify_log_excerpt": final_verify_log.splitlines()[:20],
    }
    dump_json(apply_report_file, report)
    print(json.dumps(report, ensure_ascii=False))
    return 0 if final_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
