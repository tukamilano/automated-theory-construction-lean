from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import Callable
from typing import Any

from append_derived import append_theorem
from common import read_jsonl, resolve_max_attempts, write_jsonl_atomic
from lean_verify import verify_scratch
from state_update import apply_state_update
from worker_client import invoke_worker_json, load_worker_settings


def debug_log(msg: str) -> None:
    """Print debug message to stderr with timestamp."""
    timestamp = time.strftime("%H:%M:%S")
    print(f"[{timestamp}] {msg}", file=sys.stderr, flush=True)



SCRATCH_TEMPLATE = (
    "import AutomatedTheoryConstruction.Theory\n"
    "import AutomatedTheoryConstruction.Derived\n\n"
    "namespace AutomatedTheoryConstruction\n\n"
    "-- Temporary Lean code generated for verification is written here.\n\n"
    "end AutomatedTheoryConstruction\n"
)

DERIVED_TEMPLATE = (
    "import AutomatedTheoryConstruction.Theory\n\n"
    "namespace AutomatedTheoryConstruction\n\n"
    "-- Verified theorems are appended here by scripts/append_derived.py.\n\n"
    "end AutomatedTheoryConstruction\n"
)


def normalize_stmt_text(stmt: str) -> str:
    return " ".join(stmt.split())


def is_trivial_negation_style(stmt: str) -> bool:
    normalized = normalize_stmt_text(stmt)
    return normalized.startswith("¬(") or normalized.endswith("→ False")


def pick_next_problem(open_rows: list[dict[str, Any]], max_attempts: int) -> dict[str, Any] | None:
    eligible = [row for row in open_rows if int(row.get("n", 0)) < max_attempts]
    if not eligible:
        return None
    eligible.sort(
        key=lambda row: (
            int(row.get("n", 0)),
            is_trivial_negation_style(str(row.get("stmt", ""))),
            str(row.get("id", "")),
        )
    )
    return eligible[0]


def validate_picker_output(payload: dict[str, Any], open_rows: list[dict[str, Any]], max_attempts: int) -> str:
    if "error" in payload:
        if payload.get("error") == "no_selectable_problem":
            return ""
        raise ValueError("picker output contains unsupported error value")

    allowed_keys = {"selected_problem_id"}
    if set(payload.keys()) != allowed_keys:
        raise ValueError("picker output must contain exactly one key: selected_problem_id")

    selected_id = payload.get("selected_problem_id")
    if not isinstance(selected_id, str) or not selected_id:
        raise ValueError("selected_problem_id must be a non-empty string")

    eligible_ids = {
        str(row.get("id", ""))
        for row in open_rows
        if int(row.get("n", 0)) < max_attempts
    }
    if selected_id not in eligible_ids:
        raise ValueError("selected_problem_id is not eligible under current open problems and max_attempts")
    return selected_id


def validate_prover_output(payload: dict[str, Any], expected_problem_id: str) -> tuple[str, str, str, str, list[str]]:
    required_keys = {"problem_id", "result", "proof_sketch", "proof_text", "counterexample_text", "new_problems"}
    if set(payload.keys()) != required_keys:
        raise ValueError("prover output keys mismatch required contract")

    problem_id = payload.get("problem_id")
    if problem_id != expected_problem_id:
        raise ValueError("prover output problem_id does not match picked problem")

    result = payload.get("result")
    if result not in {"proof", "counterexample", "stuck"}:
        raise ValueError("prover result must be one of: proof, counterexample, stuck")

    proof_sketch = payload.get("proof_sketch")
    proof_text = payload.get("proof_text")
    counterexample_text = payload.get("counterexample_text")
    if not isinstance(proof_sketch, str) or not isinstance(proof_text, str) or not isinstance(counterexample_text, str):
        raise ValueError("proof_sketch, proof_text and counterexample_text must be strings")

    new_problems_value = payload.get("new_problems")
    if not isinstance(new_problems_value, list):
        raise ValueError("new_problems must be an array of strings")
    if len(new_problems_value) > 2:
        raise ValueError("new_problems must have length <= 2")
    if any((not isinstance(item, str)) for item in new_problems_value):
        raise ValueError("new_problems must contain only strings")

    new_problems = [item.strip() for item in new_problems_value if item.strip()][:2]
    return result, proof_sketch, proof_text, counterexample_text, new_problems


def validate_expand_output(payload: dict[str, Any], expected_problem_id: str) -> list[str]:
    required_keys = {"problem_id", "new_problems"}
    if set(payload.keys()) != required_keys:
        raise ValueError("expand output must contain exactly: problem_id, new_problems")

    problem_id = payload.get("problem_id")
    if problem_id != expected_problem_id:
        raise ValueError("expand output problem_id does not match picked problem")

    new_problems_value = payload.get("new_problems")
    if not isinstance(new_problems_value, list):
        raise ValueError("expand new_problems must be an array of strings")
    if len(new_problems_value) > 2:
        raise ValueError("expand new_problems must have length <= 2")
    if any((not isinstance(item, str)) for item in new_problems_value):
        raise ValueError("expand new_problems must contain only strings")

    return [item.strip() for item in new_problems_value if item.strip()][:2]


def load_json_payload_from_args(inline_json: str | None, json_file: str | None) -> dict[str, Any] | None:
    if inline_json is None and json_file is None:
        return None
    if inline_json is not None and json_file is not None:
        raise ValueError("Use only one of inline JSON or JSON file input")

    raw = inline_json
    if raw is None and json_file is not None:
        raw = Path(json_file).read_text(encoding="utf-8")

    payload = json.loads(raw)
    if not isinstance(payload, dict):
        raise ValueError("JSON payload must be an object")
    return payload


def load_prompt_text(prompt_file: str) -> str:
    path = Path(prompt_file)
    if not path.exists():
        raise ValueError(f"Prompt file not found: {prompt_file}")
    return path.read_text(encoding="utf-8")


def load_optional_text(file_path: str) -> str:
    path = Path(file_path)
    if not path.exists():
        return ""
    return path.read_text(encoding="utf-8")


def write_proof_note_markdown(
    notes_dir: Path,
    *,
    problem_id: str,
    stmt: str,
    result: str,
    proof_sketch: str,
    counterexample_text: str,
    proof_text: str,
) -> tuple[Path, str]:
    """Persist natural-language reasoning as markdown for formalization reuse."""
    notes_dir.mkdir(parents=True, exist_ok=True)
    note_path = notes_dir / f"{problem_id}.md"

    sections = [
        f"# Problem {problem_id}",
        "",
        "## Statement",
        stmt.strip(),
        "",
        "## Attempt Result",
        result.strip(),
        "",
        "## Natural Language Sketch",
        (proof_sketch or "(empty)").strip(),
        "",
        "## Counterexample Intuition",
        (counterexample_text or "(empty)").strip(),
        "",
        "## Lean Draft",
        "```lean",
        (proof_text or "").rstrip(),
        "```",
        "",
    ]
    content = "\n".join(sections)
    note_path.write_text(content, encoding="utf-8")
    return note_path, content


def looks_formalizable(stmt: str) -> bool:
    """Check if stmt has basic structure to attempt formalization.
    
    Flexible approach: requires quantifier + some logical structure, not specific symbols.
    """
    simple_stmt = " ".join(stmt.split())
    
    # Must have quantifier
    has_quantifier = "∀" in simple_stmt or "∃" in simple_stmt
    if not has_quantifier:
        return False
    
    # Must have reasonable length
    if len(simple_stmt) < 10 or len(simple_stmt) > 2000:
        return False
    
    # Must have some predicate/relation (broad check: =, <, >, ≠, *, op, :, →, ∧, ∨)
    has_structure = any(sym in simple_stmt for sym in ["=", "<", ">", "≠", "*", "op", ":", "→", "∧", "∨", "¬"])
    return has_structure


def formalize_to_scratch(
    problem_id: str,
    stmt: str,
    mode: str,
    proof_text: str,
    counterexample_text: str,
    include_mathlib_import: bool,
) -> tuple[str | None, str | None]:
    if not looks_formalizable(stmt):
        return None, None

    theorem_name = f"thm_{problem_id}"
    if mode == "proof":
        raw_body = proof_text.strip() if proof_text.strip() else "sorry"
        body = "\n  ".join(line.rstrip() for line in raw_body.splitlines())
        theorem = f"theorem {theorem_name} : {stmt} := by\n  {body}\n"
    else:  # mode == "counterexample"
        # For counterexample: proof_text contains the proof that the negation holds.
        # We prove ¬(stmt), which is logically equivalent to disproving the original statement.
        # The proof_text should construct a counterexample and derive a contradiction from stmt.
        raw_body = proof_text.strip() if proof_text.strip() else "sorry"
        body = "\n  ".join(line.rstrip() for line in raw_body.splitlines())
        theorem = f"theorem {theorem_name}_is_false : ¬({stmt}) := by\n  {body}\n"

    import_block = ""
    if include_mathlib_import:
        import_block = "import Mathlib\n"

    scratch = (
        import_block
        + "import AutomatedTheoryConstruction.Theory\n"
        "import AutomatedTheoryConstruction.Derived\n\n"
        "namespace AutomatedTheoryConstruction\n\n"
        f"{theorem}\n"
        "end AutomatedTheoryConstruction\n"
    )
    return theorem_name, scratch


def parse_new_problems(raw_values: list[str]) -> list[str]:
    values: list[str] = []
    for raw in raw_values:
        text = raw.strip()
        if text:
            values.append(text)
    return values[:2]


def merge_new_problems(existing: list[str], incoming: list[str]) -> list[str]:
    """Merge and deduplicate generated problems while keeping order and cap."""
    merged: list[str] = []
    seen: set[str] = set()

    for item in list(existing) + list(incoming):
        text = str(item).strip()
        if not text:
            continue
        norm = normalize_stmt_text(text)
        if norm in seen:
            continue
        seen.add(norm)
        merged.append(text)
        if len(merged) >= 2:
            break

    return merged


def emit_phase_log(enabled: bool, phase: str, **fields: Any) -> None:
    if not enabled:
        return
    payload: dict[str, Any] = {
        "event": "phase",
        "phase": phase,
        "ts": int(time.time()),
    }
    payload.update(fields)
    print(payload, flush=True)


def is_worker_timeout_error(exc: Exception) -> bool:
    message = str(exc).lower()
    return "timed out" in message or "timeout" in message


def filter_generated_subgoals(candidates: list[str], original_stmt: str) -> list[str]:
    """Keep only meaningful, non-trivial generated subgoals.

    Rejects direct logical-negation templates and duplicates to reduce queue pollution.
    """
    original_norm = normalize_stmt_text(original_stmt)
    filtered: list[str] = []
    seen_norms: set[str] = set()

    for candidate in candidates:
        text = str(candidate).strip()
        if not text:
            continue

        norm = normalize_stmt_text(text)
        if norm == original_norm:
            continue

        # Avoid mechanical timeout templates such as ¬(P) and P → False.
        if is_trivial_negation_style(norm):
            continue

        if norm in seen_norms:
            continue
        seen_norms.add(norm)
        filtered.append(text)

    return filtered[:2]


def collect_recent_subgoal_candidates(
    memory_path: Path,
    problem_id: str,
    max_candidates: int = 16,
) -> list[str]:
    """Collect candidate subgoals from same-problem formalization memory only."""
    if not memory_path.exists():
        return []

    try:
        payload = json.loads(memory_path.read_text(encoding="utf-8"))
    except Exception:
        return []

    if not isinstance(payload, dict):
        return []

    candidates: list[str] = []

    def add_from_rows(rows: Any) -> None:
        if not isinstance(rows, list):
            return
        # Prefer latest rows first.
        for item in reversed(rows):
            if not isinstance(item, dict):
                continue
            row_candidates = item.get("new_problems", [])
            if not isinstance(row_candidates, list):
                continue
            for row_candidate in row_candidates:
                if isinstance(row_candidate, str) and row_candidate.strip():
                    candidates.append(row_candidate.strip())
                    if len(candidates) >= max_candidates:
                        return

    # Use only same-problem history to respect proof-local reasoning context.
    add_from_rows(payload.get(problem_id, []))
    return candidates[:max_candidates]


def make_timeout_subgoals(
    stmt: str,
    memory_path: Path,
    problem_id: str,
    fallback_candidates: list[str] | None = None,
) -> list[str]:
    """Generate follow-up subgoals from prior unresolved reasoning history.

    Uses prior repair/prover proposals from formalization memory and avoids synthetic
    logical-negation templates.
    """
    candidates = collect_recent_subgoal_candidates(memory_path, problem_id)

    if fallback_candidates:
        candidates.extend(fallback_candidates)

    return filter_generated_subgoals(candidates, stmt)


def extract_derived_theorem_entries(derived_path: Path, max_theorems: int = 50) -> list[dict[str, str]]:
    """Extract theorem names and one-line statements from Derived.lean."""
    if not derived_path.exists():
        return []

    try:
        content = derived_path.read_text(encoding="utf-8")
    except Exception:
        return []

    entries: list[dict[str, str]] = []
    theorem_pattern = re.compile(r"^\s*theorem\s+([A-Za-z0-9_']+)\s*:\s*(.+?)\s*:=")
    for line in content.splitlines():
        match = theorem_pattern.search(line)
        if match:
            statement = match.group(2).strip()
            if not statement:
                continue
            entries.append({"name": match.group(1), "statement": statement})
            if len(entries) >= max_theorems:
                break
    return entries


def classify_statement_shape(stmt: str) -> dict[str, bool]:
    normalized = normalize_stmt_text(stmt)
    return {
        "has_forall": "∀" in normalized,
        "has_exists": "∃" in normalized,
        "has_negation": "¬" in normalized,
        "has_mul": "*" in normalized,
        "has_eq": "=" in normalized,
        "has_subsingleton": "Subsingleton" in normalized,
    }


def extract_relevance_keywords(stmt: str) -> set[str]:
    words = re.findall(r"[A-Za-z_][A-Za-z0-9_']*", stmt)
    stopwords = {
        "Type",
        "SemigroupLike01",
        "Mul",
        "op",
        "x",
        "y",
        "z",
        "h",
        "by",
        "fun",
        "let",
        "intro",
        "have",
        "show",
    }
    keywords = {word for word in words if len(word) >= 4 and word not in stopwords}
    if "Subsingleton" in stmt:
        keywords.add("Subsingleton")
    return keywords


def same_relevance_family(target_shape: dict[str, bool], entry_shape: dict[str, bool]) -> bool:
    return (
        target_shape["has_forall"] == entry_shape["has_forall"]
        and target_shape["has_exists"] == entry_shape["has_exists"]
        and target_shape["has_negation"] == entry_shape["has_negation"]
        and target_shape["has_mul"] == entry_shape["has_mul"]
        and target_shape["has_eq"] == entry_shape["has_eq"]
        and target_shape["has_subsingleton"] == entry_shape["has_subsingleton"]
    )


def summarize_derived_statement(statement: str, max_chars: int = 120) -> str:
    text = normalize_stmt_text(statement)
    semigroup_prefix = "∀ {α : Type u} [SemigroupLike01 α], "
    if text.startswith(semigroup_prefix):
        text = text[len(semigroup_prefix) :]
    if len(text) > max_chars:
        return text[: max_chars - 3] + "..."
    return text


def shortlist_relevant_derived_entries(
    entries: list[dict[str, str]],
    stmt: str,
    max_entries: int = 5,
) -> list[dict[str, str]]:
    if not entries:
        return []

    target_norm = normalize_stmt_text(stmt)
    target_shape = classify_statement_shape(stmt)
    target_keywords = extract_relevance_keywords(stmt)
    shortlisted: list[dict[str, str]] = []
    seen_names: set[str] = set()

    def add_pass(predicate: Callable[[dict[str, str]], bool]) -> None:
        for entry in entries:
            if entry["name"] in seen_names:
                continue
            if normalize_stmt_text(entry["statement"]) == target_norm:
                continue
            if not predicate(entry):
                continue
            shortlisted.append(entry)
            seen_names.add(entry["name"])
            if len(shortlisted) >= max_entries:
                return

    def entry_shape(entry: dict[str, str]) -> dict[str, bool]:
        return classify_statement_shape(entry["statement"])

    add_pass(
        lambda entry: same_relevance_family(target_shape, entry_shape(entry))
        and bool(target_keywords & extract_relevance_keywords(entry["statement"]))
    )
    add_pass(lambda entry: same_relevance_family(target_shape, entry_shape(entry)))
    add_pass(
        lambda entry: target_shape["has_exists"] == entry_shape(entry)["has_exists"]
        and target_shape["has_negation"] == entry_shape(entry)["has_negation"]
        and target_shape["has_mul"] == entry_shape(entry)["has_mul"]
    )
    return shortlisted[:max_entries]


def render_relevant_derived_context(entries: list[dict[str, str]], max_chars: int = 1200) -> str:
    if not entries:
        return ""

    lines = [
        "",
        "-- Relevant verified theorems from Derived.lean:",
        "-- Check these theorem names before re-deriving from axioms.",
    ]
    for entry in entries:
        lines.append(f"-- {entry['name']} :: {summarize_derived_statement(entry['statement'])}")

    summary = "\n".join(lines)
    if len(summary) > max_chars:
        summary = summary[:max_chars] + "\n-- (relevant theorem list truncated)"
    return summary


def build_problem_theory_context(theory_context: str, derived_path: Path, stmt: str) -> str:
    entries = extract_derived_theorem_entries(derived_path)
    relevant_entries = shortlist_relevant_derived_entries(entries, stmt)
    relevant_summary = render_relevant_derived_context(relevant_entries)
    if relevant_summary:
        return theory_context + relevant_summary
    return theory_context


def analyze_lean_failure(stderr: str, stdout: str) -> dict[str, Any]:
    text = (stderr or "") + "\n" + (stdout or "")
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    top_lines = lines[:12]
    categories: list[str] = []

    if "Type mismatch" in text:
        categories.append("type_mismatch")
    if "rewrite` failed" in text or "Tactic `rewrite` failed" in text:
        categories.append("rewrite_failed")
    if "unsolved goals" in text:
        categories.append("unsolved_goals")
    if "unknown constant" in text or "unknown identifier" in text:
        categories.append("unknown_symbol")
    if "unknown tactic" in text:
        categories.append("unknown_tactic")
    if "Application type mismatch" in text:
        categories.append("application_type_mismatch")
    if not categories:
        categories.append("other")

    fingerprint = " | ".join(top_lines[:3]) if top_lines else "no_diagnostics"
    return {
        "fingerprint": fingerprint,
        "categories": categories,
        "top_lines": top_lines,
    }


def load_formalization_memory(memory_path: Path, problem_id: str) -> list[dict[str, Any]]:
    if not memory_path.exists():
        return []
    try:
        payload = json.loads(memory_path.read_text(encoding="utf-8"))
    except Exception:
        return []
    if not isinstance(payload, dict):
        return []
    rows = payload.get(problem_id, [])
    if not isinstance(rows, list):
        return []
    safe_rows: list[dict[str, Any]] = []
    for item in rows:
        if not isinstance(item, dict):
            continue
        raw_new_problems = item.get("new_problems", [])
        parsed_new_problems: list[str] = []
        if isinstance(raw_new_problems, list):
            parsed_new_problems = [str(v).strip() for v in raw_new_problems if str(v).strip()]
        safe_rows.append(
            {
                "result": str(item.get("result", "")),
                "verify_success": bool(item.get("verify_success", False)),
                "proof_sketch": str(item.get("proof_sketch", "")),
                "proof_text": str(item.get("proof_text", "")),
                "counterexample_text": str(item.get("counterexample_text", "")),
                "lean_error_excerpt": str(item.get("lean_error_excerpt", "")),
                "lean_error_fingerprint": str(item.get("lean_error_fingerprint", "")),
                "new_problems": parsed_new_problems[:2],
            }
        )
    return safe_rows


def save_formalization_memory(memory_path: Path, problem_id: str, history: list[dict[str, Any]]) -> None:
    memory_path.parent.mkdir(parents=True, exist_ok=True)
    payload: dict[str, Any] = {}
    if memory_path.exists():
        try:
            existing = json.loads(memory_path.read_text(encoding="utf-8"))
            if isinstance(existing, dict):
                payload = existing
        except Exception:
            payload = {}
    payload[problem_id] = history[-20:]
    memory_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")


def query_prover_with_retries(
    worker_settings: Any,
    prover_prompt: str,
    problem_id: str,
    stmt: str,
    open_rows: list[dict[str, Any]],
    max_attempts: int,
    prover_retries: int,
    theory_context: str,
    memory_path: Path,
) -> tuple[str, str, str, str, list[str], int, dict[str, Any]]:
    retries = max(1, prover_retries)
    last_result = "stuck"
    last_proof_sketch = ""
    last_proof_text = ""
    last_counterexample_text = ""
    last_new_problems: list[str] = []
    last_worker_meta: dict[str, Any] = {}

    for attempt in range(1, retries + 1):
        payload: dict[str, Any] = {
            "problem_id": problem_id,
            "stmt": stmt,
            "theory_context": theory_context,
            "open_problems": open_rows,
            "max_attempts": max_attempts,
            "prover_attempt_index": attempt,
            "prover_attempt_budget": retries,
            "mathlib_allowed": True,
            "new_problem_generation_policy": {
                "prefer_generalization": True,
                "avoid_direct_axiom_instantiation": True,
                "avoid_variable_renaming_only": True,
                "target_novelty": "medium_or_high",
                "examples_of_boring_patterns": [
                    "x x duplicates only",
                    "single-axiom restatement",
                    "commutativity/idempotence restatement",
                ],
            },
        }
        if attempt > 1:
            payload["retry_instruction"] = (
                "Previous attempt returned stuck. Try a different angle. "
                "If you still cannot prove or refute, return at least one concrete "
                "counterexample candidate in counterexample_text and up to two useful new_problems."
            )
            payload["previous_result"] = last_result
            payload["previous_proof_sketch"] = last_proof_sketch
            payload["previous_counterexample_text"] = last_counterexample_text
            payload["previous_new_problems"] = last_new_problems

        try:
            debug_log(f"Calling prover for problem {problem_id}, attempt {attempt}/{retries}")
            prover_start = time.monotonic()
            prover_payload, worker_meta = invoke_worker_json(
                settings=worker_settings,
                task_type="prover",
                system_prompt=prover_prompt,
                payload=payload,
                metadata={"problem_id": problem_id, "attempt": attempt},
            )
            last_worker_meta = worker_meta
            prover_elapsed = time.monotonic() - prover_start
            debug_log(f"Prover returned for {problem_id}: {prover_payload.get('result', 'unknown')} (took {prover_elapsed:.1f}s)")
        except RuntimeError as exc:
            if is_worker_timeout_error(exc):
                debug_log(f"Prover timed out for {problem_id}: {exc}")
                timeout_sketch = (
                    "Prover worker timed out before returning a valid response. "
                    "Treating this iteration as stuck so the problem remains open and n increments. "
                    f"Details: {exc}"
                )
                timeout_subgoals = make_timeout_subgoals(
                    stmt=stmt,
                    memory_path=memory_path,
                    problem_id=problem_id,
                    fallback_candidates=last_new_problems,
                )
                return "stuck", timeout_sketch, "", "", timeout_subgoals, attempt, last_worker_meta
            raise
        result, proof_sketch, proof_text, counterexample_text, new_problems = validate_prover_output(prover_payload, problem_id)

        last_result = result
        last_proof_sketch = proof_sketch
        last_proof_text = proof_text
        last_counterexample_text = counterexample_text
        last_new_problems = new_problems

        if result != "stuck":
            return result, proof_sketch, proof_text, counterexample_text, new_problems, attempt, last_worker_meta

    return (
        last_result,
        last_proof_sketch,
        last_proof_text,
        last_counterexample_text,
        last_new_problems,
        retries,
        last_worker_meta,
    )


def attempt_formalization_until_timeout(
    *,
    problem_id: str,
    stmt: str,
    result: str,
    proof_sketch: str,
    proof_text: str,
    counterexample_text: str,
    new_problems: list[str],
    scratch_file: Path,
    skip_verify: bool,
    worker_settings: Any,
    prover_prompt: str,
    open_rows: list[dict[str, Any]],
    max_attempts: int,
    theory_context: str,
    verify_timeout_sec: int = 180,
    formalization_retry_budget_sec: int,
    memory_path: Path,
    natural_language_note_markdown: str,
    natural_language_note_path: str,
    phase_logger: Callable[..., None] | None = None,
) -> tuple[bool, str | None, str, str, str, list[str], str]:
    verify_success = False
    theorem_name: str | None = None
    verify_error_excerpt = ""
    include_mathlib_import = False
    retained_new_problems = list(new_problems)

    if result not in {"proof", "counterexample"}:
        # Preserve stuck/counterexample exploration history so future timeout handling
        # can mine subgoal candidates from prior reasoning.
        persisted_history = load_formalization_memory(memory_path, problem_id)
        persisted_history.append(
            {
                "result": result,
                "verify_success": verify_success,
                "proof_sketch": proof_sketch,
                "proof_text": proof_text,
                "counterexample_text": counterexample_text,
                "lean_error_excerpt": verify_error_excerpt,
                "lean_error_fingerprint": "non_formalized_result",
                "new_problems": list(new_problems)[:2],
            }
        )
        save_formalization_memory(memory_path, problem_id, persisted_history)
        return verify_success, theorem_name, result, proof_text, counterexample_text, new_problems, verify_error_excerpt

    deadline = time.monotonic() + max(1, formalization_retry_budget_sec)
    persisted_history = load_formalization_memory(memory_path, problem_id)
    repair_round = 0
    repair_history: list[dict[str, Any]] = list(persisted_history)

    while True:
        if phase_logger is not None:
            phase_logger(
                phase="formalize_and_verify",
                problem_id=problem_id,
                result=result,
                repair_round=repair_round,
            )
        theorem_name, scratch_code = formalize_to_scratch(
            problem_id=problem_id,
            stmt=stmt,
            mode=result,
            proof_text=proof_text,
            counterexample_text=counterexample_text,
            include_mathlib_import=include_mathlib_import,
        )

        lean_diagnostics = ""
        if scratch_code is None:
            verify_error_excerpt = "formalization failed before Lean check"
            verify_error_analysis = {
                "fingerprint": "formalization_failed_before_lean",
                "categories": ["formalization_failed"],
                "top_lines": [verify_error_excerpt],
            }
        else:
            scratch_file.write_text(scratch_code, encoding="utf-8")
            if skip_verify:
                verify_success = True
                verify_error_analysis = {
                    "fingerprint": "verify_skipped",
                    "categories": ["verify_skipped"],
                    "top_lines": [],
                }
            else:
                verify_result = verify_scratch(problem_id, result, scratch_file, timeout_sec=verify_timeout_sec)
                verify_success = bool(verify_result.get("success", False))
                lean_diagnostics = (
                    str(verify_result.get("stderr", "")) + "\n" + str(verify_result.get("stdout", ""))
                ).strip()
                if not verify_success:
                    verify_stderr = str(verify_result.get("stderr", "")).strip()
                    verify_stdout = str(verify_result.get("stdout", "")).strip()
                    verify_error_excerpt = (verify_stderr or verify_stdout).splitlines()[0] if (verify_stderr or verify_stdout) else "Lean verification failed"
                verify_error_analysis = analyze_lean_failure(
                    str(verify_result.get("stderr", "")),
                    str(verify_result.get("stdout", "")),
                )

            if verify_success:
                success_fingerprint = str(verify_error_analysis.get("fingerprint", "verified"))
                repair_history.append(
                    {
                        "result": result,
                        "verify_success": True,
                        "proof_sketch": proof_sketch,
                        "proof_text": proof_text,
                        "counterexample_text": counterexample_text,
                        "lean_error_excerpt": verify_error_excerpt,
                        "lean_error_fingerprint": success_fingerprint,
                        "new_problems": list(retained_new_problems)[:2],
                    }
                )
                if len(repair_history) > 20:
                    repair_history = repair_history[-20:]
                save_formalization_memory(memory_path, problem_id, repair_history)
                return (
                    verify_success,
                    theorem_name,
                    result,
                    proof_text,
                    counterexample_text,
                    retained_new_problems,
                    verify_error_excerpt,
                )

        if worker_settings is None or time.monotonic() >= deadline:
            save_formalization_memory(memory_path, problem_id, repair_history)
            return (
                verify_success,
                theorem_name,
                result,
                proof_text,
                counterexample_text,
                retained_new_problems,
                verify_error_excerpt,
            )

        error_fingerprint = str(verify_error_analysis.get("fingerprint", "no_diagnostics"))

        repair_history.append(
            {
                "result": result,
                "verify_success": verify_success,
                "proof_sketch": proof_sketch,
                "proof_text": proof_text,
                "counterexample_text": counterexample_text,
                "lean_error_excerpt": verify_error_excerpt,
                "lean_error_fingerprint": error_fingerprint,
                "new_problems": list(new_problems)[:2],
            }
        )
        if len(repair_history) > 4:
            repair_history = repair_history[-20:]
        save_formalization_memory(memory_path, problem_id, repair_history)

        repair_round += 1
        if phase_logger is not None:
            phase_logger(
                phase="repair",
                problem_id=problem_id,
                repair_round=repair_round,
                error_fingerprint=error_fingerprint,
            )
        repair_payload: dict[str, Any] = {
            "problem_id": problem_id,
            "stmt": stmt,
            "theory_context": theory_context,
            "open_problems": open_rows,
            "max_attempts": max_attempts,
            "prover_attempt_index": repair_round,
            "prover_attempt_budget": "until_formalization_timeout",
            "mathlib_allowed": True,
            "new_problem_generation_policy": {
                "prefer_generalization": True,
                "avoid_direct_axiom_instantiation": True,
                "avoid_variable_renaming_only": True,
                "target_novelty": "medium_or_high",
            },
            "retry_instruction": (
                "Previous proof/counterexample failed Lean formalization or verification. "
                "Read the Lean diagnostics carefully. Revise proof_sketch if the strategy was wrong, "
                "then fix proof_text to match. proof_text must be Lean tactic code only."
            ),
            "error_fingerprint": error_fingerprint,
            "error_categories": verify_error_analysis.get("categories", []),
            "previous_result": result,
            "previous_proof_sketch": proof_sketch,
            "previous_proof_text": proof_text,
            "previous_counterexample_text": counterexample_text,
            "previous_new_problems": new_problems,
            "natural_language_proof_note_markdown": natural_language_note_markdown,
            "natural_language_proof_note_path": natural_language_note_path,
            "repair_history_tail": repair_history[-8:],
            "lean_error_excerpt": verify_error_excerpt,
            "lean_error_top_lines": verify_error_analysis.get("top_lines", []),
            "lean_diagnostics": "\n".join(lean_diagnostics.splitlines()[:60]),
            "current_scratch_code": scratch_code or "",
            "mathlib_import_in_scratch": include_mathlib_import,
            "deadline_note": "Keep trying corrections until a Lean-checkable output is found.",
        }

        try:
            repaired, _ = invoke_worker_json(
                settings=worker_settings,
                task_type="repair",
                system_prompt=prover_prompt,
                payload=repair_payload,
                metadata={"problem_id": problem_id, "repair_round": repair_round},
            )
        except RuntimeError as exc:
            if is_worker_timeout_error(exc):
                verify_error_excerpt = f"repair worker timeout: {exc}"
                save_formalization_memory(memory_path, problem_id, repair_history)
                return (
                    verify_success,
                    theorem_name,
                    result,
                    proof_text,
                    counterexample_text,
                    retained_new_problems,
                    verify_error_excerpt,
                )
            raise
        try:
            result, proof_sketch, proof_text, counterexample_text, new_problems = validate_prover_output(repaired, problem_id)
            retained_new_problems = merge_new_problems(retained_new_problems, new_problems)
        except ValueError as exc:
            verify_error_excerpt = f"repair output invalid: {exc}"
            continue

        # Keep default path lightweight. Enable Mathlib import only when diagnostics suggest missing tactics/symbols.
        categories = verify_error_analysis.get("categories", [])
        if "unknown_tactic" in categories or "unknown_symbol" in categories:
            include_mathlib_import = True


def initialize_runtime_state(
    data_dir: Path,
    seeds_file: Path,
    scratch_file: Path,
    reset_scratch: bool,
    derived_file: Path,
    reset_derived: bool,
    formalization_memory_file: Path,
    reset_formalization_memory: bool,
) -> None:
    seed_rows = read_jsonl(seeds_file)
    if not seed_rows:
        raise ValueError(f"Seeds file is empty: {seeds_file}")

    data_dir.mkdir(parents=True, exist_ok=True)
    write_jsonl_atomic(data_dir / "open_problems.jsonl", seed_rows)
    write_jsonl_atomic(data_dir / "solved_problems.jsonl", [])
    write_jsonl_atomic(data_dir / "counterexamples.jsonl", [])

    if reset_scratch:
        scratch_file.parent.mkdir(parents=True, exist_ok=True)
        scratch_file.write_text(SCRATCH_TEMPLATE, encoding="utf-8")

    if reset_derived:
        derived_file.parent.mkdir(parents=True, exist_ok=True)
        derived_file.write_text(DERIVED_TEMPLATE, encoding="utf-8")

    if reset_formalization_memory:
        formalization_memory_file.parent.mkdir(parents=True, exist_ok=True)
        formalization_memory_file.write_text("{}\n", encoding="utf-8")


def prebuild_lean_project() -> None:
    """Build Lean artifacts once during initialization.

    This keeps heavy compilation outside the per-problem solving path.
    """
    proc = subprocess.run(
        ["lake", "build"],
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        stderr = (proc.stderr or "").strip()
        stdout = (proc.stdout or "").strip()
        excerpt = stderr or stdout or "lake build failed without output"
        raise RuntimeError(f"Initialization build failed: {excerpt}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Run one iteration of the minimal prototype loop.")
    parser.add_argument("--initialize-on-start", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--enable-worker", action="store_true")
    parser.add_argument("--worker-command")
    parser.add_argument("--worker-timeout", type=int, default=300)
    parser.add_argument("--phase-logs", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--skip-verify", action="store_true")
    args = parser.parse_args()

    # Fixed runtime paths and hidden compatibility defaults.
    args.data_dir = "data"
    args.config = "config/defaults.json"
    args.seeds_file = "theories/semigroup_like_01/seeds.jsonl"
    args.scratch_file = "AutomatedTheoryConstruction/Scratch.lean"
    args.derived_file = "AutomatedTheoryConstruction/Derived.lean"
    args.proof_notes_dir = "data/proof_notes"
    args.reset_scratch_on_start = True
    args.reset_derived_on_start = True
    args.max_attempts = None
    args.picker_output_json = None
    args.picker_output_file = None
    args.prover_output_json = None
    args.prover_output_file = None
    args.theory_file = "AutomatedTheoryConstruction/Theory.lean"
    # Use simplified prover prompt for worker (picker is now deterministic local logic)
    args.prover_prompt_file = "prompts/prover_interactive.md"
    args.expander_prompt_file = "prompts/new_problem_expander.md"
    args.prover_retries = 2
    args.formalization_retry_budget_sec = 300
    args.formalization_memory_file = "data/formalization_memory.json"
    args.reset_formalization_memory_on_start = True
    args.mock_result = "stuck"
    args.mock_proof_text = ""
    args.mock_counterexample_text = ""
    args.mock_new_problem = []

    data_dir = Path(args.data_dir)
    config_path = Path(args.config)
    scratch_file = Path(args.scratch_file)
    memory_path = Path(args.formalization_memory_file)
    proof_notes_dir = Path(args.proof_notes_dir)

    if args.initialize_on_start:
        initialize_runtime_state(
            data_dir=data_dir,
            seeds_file=Path(args.seeds_file),
            scratch_file=scratch_file,
            reset_scratch=args.reset_scratch_on_start,
            derived_file=Path(args.derived_file),
            reset_derived=args.reset_derived_on_start,
            formalization_memory_file=memory_path,
            reset_formalization_memory=args.reset_formalization_memory_on_start,
        )
        debug_log("Running lake build during initialization")
        prebuild_lean_project()
        debug_log("Initialization build completed")

    max_attempts = resolve_max_attempts(args.max_attempts, config_path)
    base_theory_context = load_optional_text(args.theory_file)
    derived_path = Path(args.derived_file)
    open_path = data_dir / "open_problems.jsonl"

    worker_settings = None
    if args.enable_worker:
        worker_settings = load_worker_settings(
            command_override=args.worker_command,
            timeout_override=args.worker_timeout,
        )
    completed_iterations = 0
    while True:
        if not open_path.exists():
            print({"status": "open_problems_missing", "iterations_completed": completed_iterations})
            return

        open_rows = read_jsonl(open_path)
        if not open_rows:
            print({"status": "no_open_problems", "iterations_completed": completed_iterations})
            return

        eligible_rows = [row for row in open_rows if int(row.get("n", 0)) < max_attempts]
        if not eligible_rows:
            print({
                "status": "no_eligible_open_problem",
                "max_attempts": max_attempts,
                "iterations_completed": completed_iterations,
            })
            return

        iteration_num = completed_iterations + 1
        debug_log(f"=== Iteration {iteration_num} START ===")
        debug_log(f"{len(open_rows)} total problems, {len(eligible_rows)} eligible (n < {max_attempts})")

        emit_phase_log(
            args.phase_logs,
            "iteration_start",
            iteration=completed_iterations + 1,
            open_problem_count=len(open_rows),
            eligible_problem_count=len(eligible_rows),
        )

        # Select problem using local deterministic logic, no LLM needed
        debug_log(f"Selecting problem locally from {len(eligible_rows)} eligible problems")
        picked = pick_next_problem(open_rows, max_attempts)

        if picked is None:
            print({
                "status": "no_eligible_open_problem",
                "max_attempts": max_attempts,
                "iterations_completed": completed_iterations,
            })
            return

        problem_id = str(picked["id"])
        stmt = str(picked.get("stmt", ""))
        theory_context = build_problem_theory_context(base_theory_context, derived_path, stmt)
        emit_phase_log(args.phase_logs, "problem_selected", iteration=completed_iterations + 1, problem_id=problem_id)

        prover_payload = load_json_payload_from_args(args.prover_output_json, args.prover_output_file)
        prover_attempts_used = 1
        proof_sketch = ""
        prover_worker_meta: dict[str, Any] = {}
        if prover_payload is not None:
            emit_phase_log(args.phase_logs, "prover", iteration=completed_iterations + 1, problem_id=problem_id, mode="provided")
            result, proof_sketch, proof_text, counterexample_text, new_problems = validate_prover_output(prover_payload, problem_id)
        elif worker_settings is not None:
            emit_phase_log(args.phase_logs, "prover", iteration=completed_iterations + 1, problem_id=problem_id, mode="worker")
            prover_prompt = load_prompt_text(args.prover_prompt_file)
            result, proof_sketch, proof_text, counterexample_text, new_problems, prover_attempts_used, prover_worker_meta = query_prover_with_retries(
                worker_settings=worker_settings,
                prover_prompt=prover_prompt,
                problem_id=problem_id,
                stmt=stmt,
                open_rows=open_rows,
                max_attempts=max_attempts,
                prover_retries=args.prover_retries,
                theory_context=theory_context,
                memory_path=memory_path,
            )
            emit_phase_log(
                args.phase_logs,
                "worker_parse",
                iteration=completed_iterations + 1,
                problem_id=problem_id,
                json_parse_attempts=int(prover_worker_meta.get("json_parse_attempts", 0) or 0),
                raw_parse_fallback_used=bool(prover_worker_meta.get("raw_parse_fallback_used", False)),
                client_json_parse_attempts=int(prover_worker_meta.get("client_json_parse_attempts", 0) or 0),
                client_raw_parse_fallback_used=bool(prover_worker_meta.get("client_raw_parse_fallback_used", False)),
            )
        else:
            emit_phase_log(args.phase_logs, "prover", iteration=completed_iterations + 1, problem_id=problem_id, mode="mock")
            result = args.mock_result
            proof_text = args.mock_proof_text
            counterexample_text = args.mock_counterexample_text
            new_problems = parse_new_problems(args.mock_new_problem)

        note_path, note_markdown = write_proof_note_markdown(
            proof_notes_dir,
            problem_id=problem_id,
            stmt=stmt,
            result=result,
            proof_sketch=proof_sketch,
            counterexample_text=counterexample_text,
            proof_text=proof_text,
        )

        prover_prompt_for_repair = load_prompt_text(args.prover_prompt_file) if worker_settings is not None else ""
        (
            verify_success,
            theorem_name,
            result,
            proof_text,
            counterexample_text,
            new_problems,
            verify_error_excerpt,
        ) = attempt_formalization_until_timeout(
            problem_id=problem_id,
            stmt=stmt,
            result=result,
            proof_sketch=proof_sketch,
            proof_text=proof_text,
            counterexample_text=counterexample_text,
            new_problems=new_problems,
            scratch_file=scratch_file,
            skip_verify=args.skip_verify,
            worker_settings=worker_settings,
            prover_prompt=prover_prompt_for_repair,
            open_rows=open_rows,
            max_attempts=max_attempts,
            theory_context=theory_context,
            verify_timeout_sec=180,
            formalization_retry_budget_sec=args.formalization_retry_budget_sec,
            memory_path=memory_path,
            natural_language_note_markdown=note_markdown,
            natural_language_note_path=str(note_path),
            phase_logger=(lambda **fields: emit_phase_log(args.phase_logs, iteration=completed_iterations + 1, **fields)),
        )
        solver_new_problem_suggestions = list(new_problems)
        expander_new_problem_suggestions: list[str] = []
        expander_worker_meta: dict[str, Any] = {}

        if worker_settings is not None:
            emit_phase_log(
                args.phase_logs,
                "expand",
                iteration=completed_iterations + 1,
                problem_id=problem_id,
                mode="worker",
            )
            expand_prompt = load_prompt_text(args.expander_prompt_file)
            same_problem_history_tail = load_formalization_memory(memory_path, problem_id)[-8:]
            expand_payload: dict[str, Any] = {
                "problem_id": problem_id,
                "stmt": stmt,
                "result": result,
                "verify_success": verify_success,
                "theory_context": theory_context,
                "existing_new_problems": list(new_problems),
                "verify_error_excerpt": verify_error_excerpt,
                "same_problem_history_tail": same_problem_history_tail,
            }
            try:
                expander_payload, expander_worker_meta = invoke_worker_json(
                    settings=worker_settings,
                    task_type="expand",
                    system_prompt=expand_prompt,
                    payload=expand_payload,
                    metadata={"problem_id": problem_id, "iteration": completed_iterations + 1},
                )
                expander_new_problem_suggestions = validate_expand_output(expander_payload, problem_id)
                new_problems = merge_new_problems(new_problems, expander_new_problem_suggestions)
                emit_phase_log(
                    args.phase_logs,
                    "expand_result",
                    iteration=completed_iterations + 1,
                    problem_id=problem_id,
                    generated_count=len(expander_new_problem_suggestions),
                    final_count=len(new_problems),
                )
            except (RuntimeError, ValueError) as exc:
                debug_log(f"Expander failed for {problem_id}: {exc}")
                emit_phase_log(
                    args.phase_logs,
                    "expand_error",
                    iteration=completed_iterations + 1,
                    problem_id=problem_id,
                    error=str(exc),
                )

        if verify_success and result in {"proof", "counterexample"}:
            scratch_code = scratch_file.read_text(encoding="utf-8")
            theorem_body_match = re.search(
                r"namespace AutomatedTheoryConstruction\n\n(.*)\nend AutomatedTheoryConstruction",
                scratch_code,
                re.DOTALL,
            )
            if theorem_body_match:
                # Auto-detect theorem name from the extracted theorem body so
                # counterexample names like `<base>_is_false` are handled correctly.
                append_theorem(Path(args.derived_file), theorem_body_match.group(1), None)

        report = apply_state_update(
            data_dir=data_dir,
            config_path=config_path,
            problem_id=problem_id,
            result=result,
            verify_success=verify_success,
            theorem_name=theorem_name,
            new_problems=new_problems,
            max_attempts_override=args.max_attempts,
        )
        emit_phase_log(args.phase_logs, "state_update", iteration=completed_iterations + 1, problem_id=problem_id)
        completed_iterations += 1
        debug_log(f"=== Iteration {completed_iterations} END ({result}, verify={verify_success}) ===\n")
        report["picked_problem_id"] = problem_id
        report["result"] = result
        report["verify_success"] = verify_success
        report["verify_error_excerpt"] = verify_error_excerpt
        report["prover_attempts_used"] = prover_attempts_used
        report["prover_proof_sketch"] = proof_sketch
        report["prover_counterexample_text"] = counterexample_text
        report["prover_new_problem_suggestions"] = solver_new_problem_suggestions
        report["expander_new_problem_suggestions"] = expander_new_problem_suggestions
        report["final_new_problems"] = new_problems
        report["proof_note_path"] = str(note_path)
        report["worker_json_parse_attempts"] = int(prover_worker_meta.get("json_parse_attempts", 0) or 0)
        report["worker_raw_parse_fallback_used"] = bool(prover_worker_meta.get("raw_parse_fallback_used", False))
        report["client_json_parse_attempts"] = int(prover_worker_meta.get("client_json_parse_attempts", 0) or 0)
        report["client_raw_parse_fallback_used"] = bool(prover_worker_meta.get("client_raw_parse_fallback_used", False))
        report["expander_worker_json_parse_attempts"] = int(expander_worker_meta.get("json_parse_attempts", 0) or 0)
        report["expander_worker_raw_parse_fallback_used"] = bool(expander_worker_meta.get("raw_parse_fallback_used", False))
        report["expander_client_json_parse_attempts"] = int(expander_worker_meta.get("client_json_parse_attempts", 0) or 0)
        report["expander_client_raw_parse_fallback_used"] = bool(expander_worker_meta.get("client_raw_parse_fallback_used", False))
        report["iteration"] = completed_iterations
        print(report)


if __name__ == "__main__":
    main()
