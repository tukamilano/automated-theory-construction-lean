from __future__ import annotations

import re
import subprocess
import threading
from pathlib import Path
from typing import Any

from append_derived import append_theorem
from common import write_json_atomic
from loop_helpers import append_derived_entry_cache
from loop_helpers import debug_log
from loop_helpers import extract_theorem_code_from_scratch
from loop_helpers import load_theory_state
from loop_helpers import theory_state_path


LEAN_VERIFY_LOCK = threading.Lock()
DERIVED_UPDATE_LOCK = threading.Lock()


def text_contains_sorry(text: str) -> bool:
    return bool(re.search(r"\bsorry\b", text))


def persist_derived_generation(
    data_dir: Path,
    *,
    generation: int,
    run_id: str,
    current_iteration: int,
) -> dict[str, Any]:
    payload = load_theory_state(data_dir)
    if not payload:
        payload = {
            "version": 1,
            "updated_at_iteration": current_iteration,
            "updated_at_run_id": run_id,
            "theory_snapshot": "",
            "next_direction": {},
            "important_verified_counterexamples": [],
            "research_agenda": {},
            "desired_summary_changes": [],
            "current_bottlenecks": [],
            "overexplored_patterns": [],
            "missing_bridges": [],
            "agenda_pressure": [],
            "summary_basis": {
                "derived_theorem_count": 0,
                "open_problem_count": 0,
                "archived_problem_count": 0,
            },
        }
    payload["derived_generation"] = int(generation)
    payload["updated_at_iteration"] = current_iteration
    payload["updated_at_run_id"] = run_id
    write_json_atomic(theory_state_path(data_dir), payload)
    return payload


def append_verified_theorem_from_scratch(
    *,
    scratch_path: Path,
    derived_file: Path,
    derived_entries: list[dict[str, str]],
    docstring: str,
    rebuild_derived: bool = True,
) -> str:
    theorem_code = extract_theorem_code_from_scratch(scratch_path)
    if not theorem_code:
        debug_log(f"extract_theorem_code_from_scratch returned empty for {scratch_path}")
        return ""
    if text_contains_sorry(theorem_code):
        debug_log(f"Refusing to append theorem containing sorry from {scratch_path}")
        return ""
    entry = extract_derived_entry_from_theorem_code(theorem_code)
    theorem_name = str(entry.get("name", "")).strip() if isinstance(entry, dict) else ""
    if not theorem_name:
        theorem_matches = list(DERIVED_THEOREM_HEADER_PATTERN.finditer(theorem_code))
        if not theorem_matches:
            debug_log(f"Could not extract theorem entry from {scratch_path}")
            return ""
        theorem_name = str(theorem_matches[-1].group(1)).strip()
    if not theorem_name:
        debug_log(f"Could not extract theorem name from {scratch_path}")
        return ""
    with LEAN_VERIFY_LOCK:
        with DERIVED_UPDATE_LOCK:
            original_content = derived_file.read_text(encoding="utf-8") if derived_file.exists() else ""
            appended = append_theorem(
                derived_file,
                theorem_code,
                theorem_name,
                docstring,
            )
            if appended:
                if rebuild_derived:
                    build_proc = subprocess.run(
                        ["lake", "build", "AutomatedTheoryConstruction.Derived"],
                        capture_output=True,
                        text=True,
                        check=False,
                    )
                    if build_proc.returncode != 0:
                        derived_file.write_text(original_content, encoding="utf-8")
                        stderr = (build_proc.stderr or "").strip()
                        stdout = (build_proc.stdout or "").strip()
                        excerpt = stderr or stdout or "lake build AutomatedTheoryConstruction.Derived failed without output"
                        raise RuntimeError(f"Failed to rebuild Derived after appending theorem: {excerpt}")
                append_derived_entry_cache(derived_entries, theorem_code)
                return theorem_code
            derived_content = derived_file.read_text(encoding="utf-8") if derived_file.exists() else ""
            if re.search(rf"\btheorem\s+{re.escape(theorem_name)}\b", derived_content):
                debug_log(
                    f"Derived.lean already contains theorem {theorem_name}; treating as already-appended from scratch {scratch_path}"
                )
                return theorem_code
            debug_log(
                f"append_theorem reported no-op for {theorem_name} from {scratch_path}; Derived.lean not changed"
            )
    return ""


def commit_verified_theorem_and_generation(
    *,
    scratch_path: Path,
    derived_file: Path,
    derived_entries: list[dict[str, str]],
    docstring: str,
    data_dir: Path,
    derived_runtime_state: dict[str, Any],
    run_id: str,
    current_iteration: int,
    rebuild_derived: bool = True,
) -> str:
    committed_theorem_code = append_verified_theorem_from_scratch(
        scratch_path=scratch_path,
        derived_file=derived_file,
        derived_entries=derived_entries,
        docstring=docstring,
        rebuild_derived=rebuild_derived,
    )
    if committed_theorem_code:
        next_generation = int(derived_runtime_state.get("generation", 0) or 0) + 1
        derived_runtime_state["generation"] = next_generation
        persist_derived_generation(
            data_dir,
            generation=next_generation,
            run_id=run_id,
            current_iteration=current_iteration,
        )
    return committed_theorem_code


DERIVED_THEOREM_HEADER_PATTERN = re.compile(r"\btheorem\s+([A-Za-z0-9_']+)\b")


def extract_derived_entry_from_theorem_code(theorem_code: str) -> dict[str, str] | None:
    theorem_code = theorem_code.strip()
    if not theorem_code:
        return None

    matches = list(DERIVED_THEOREM_HEADER_PATTERN.finditer(theorem_code))
    if not matches:
        return None

    theorem_name = ""
    statement = ""
    for match in matches:
        candidate_name = str(match.group(1)).strip()
        if not candidate_name:
            continue
        start = match.end()
        separator_index = -1
        paren_depth = 0
        bracket_depth = 0
        brace_depth = 0

        for index in range(start, len(theorem_code) - 1):
            ch = theorem_code[index]
            nxt = theorem_code[index + 1]
            if ch == "(":
                paren_depth += 1
            elif ch == ")":
                paren_depth = max(paren_depth - 1, 0)
            elif ch == "[":
                bracket_depth += 1
            elif ch == "]":
                bracket_depth = max(bracket_depth - 1, 0)
            elif ch == "{":
                brace_depth += 1
            elif ch == "}":
                brace_depth = max(brace_depth - 1, 0)
            elif (
                ch == ":"
                and nxt == "="
                and paren_depth == 0
                and bracket_depth == 0
                and brace_depth == 0
            ):
                separator_index = index
                break

        if separator_index < 0:
            continue
        candidate_statement = " ".join(theorem_code[start:separator_index].strip().split())
        if candidate_statement:
            theorem_name = candidate_name
            statement = candidate_statement

    if not theorem_name or not statement:
        return None
    return {
        "name": theorem_name,
        "statement": statement,
    }
