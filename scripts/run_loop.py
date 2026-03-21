from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import Callable
from typing import Any

from append_derived import (
    append_theorem,
    build_derived_entries_from_file,
)
from common import read_jsonl, write_jsonl_atomic
from lean_verify import verify_scratch
from state_update import apply_state_update
from worker_client import invoke_worker_json, load_task_worker_settings, load_worker_settings


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
    "-- Verified theorems and helper aliases are appended here by scripts/append_derived.py.\n"
    "-- Keep any short theorem docstrings/comments here instead of a separate metadata index.\n\n"
    "end AutomatedTheoryConstruction\n"
)


def normalize_stmt_text(stmt: str) -> str:
    return " ".join(stmt.split())


def is_trivial_negation_style(stmt: str) -> bool:
    normalized = normalize_stmt_text(stmt)
    return normalized.startswith("¬(") or normalized.endswith("→ False")


def pick_next_problem(open_rows: list[dict[str, Any]]) -> dict[str, Any] | None:
    return open_rows[0] if open_rows else None


def validate_prover_output(payload: dict[str, Any], expected_problem_id: str) -> tuple[str, str, str, list[str]]:
    required_keys = {"problem_id", "result", "proof_sketch", "counterexample_text", "new_problems"}
    if set(payload.keys()) != required_keys:
        raise ValueError("prover output keys mismatch required contract")

    problem_id = payload.get("problem_id")
    if problem_id != expected_problem_id:
        raise ValueError("prover output problem_id does not match picked problem")

    result = payload.get("result")
    if result not in {"proof", "counterexample", "stuck"}:
        raise ValueError("prover result must be one of: proof, counterexample, stuck")

    proof_sketch = payload.get("proof_sketch")
    counterexample_text = payload.get("counterexample_text")
    if not isinstance(proof_sketch, str) or not isinstance(counterexample_text, str):
        raise ValueError("proof_sketch and counterexample_text must be strings")

    new_problems_value = payload.get("new_problems")
    if not isinstance(new_problems_value, list):
        raise ValueError("new_problems must be an array of strings")
    if len(new_problems_value) > 2:
        raise ValueError("new_problems must have length <= 2")
    if any((not isinstance(item, str)) for item in new_problems_value):
        raise ValueError("new_problems must contain only strings")

    new_problems = [item.strip() for item in new_problems_value if item.strip()][:2]
    return result, proof_sketch, counterexample_text, new_problems


def validate_prover_statement_output(payload: dict[str, Any], expected_problem_id: str) -> tuple[str, str, str]:
    required_keys = {"problem_id", "result", "lean_statement", "notes"}
    if set(payload.keys()) != required_keys:
        raise ValueError("prover_statement output must contain exactly: problem_id, result, lean_statement, notes")

    problem_id = payload.get("problem_id")
    if problem_id != expected_problem_id:
        raise ValueError("prover_statement output problem_id does not match picked problem")

    result = payload.get("result")
    if result not in {"ok", "stuck"}:
        raise ValueError("prover_statement result must be one of: ok, stuck")

    lean_statement = payload.get("lean_statement")
    notes = payload.get("notes")
    if not isinstance(lean_statement, str) or not isinstance(notes, str):
        raise ValueError("prover_statement lean_statement and notes must be strings")
    if result == "ok" and not lean_statement.strip():
        raise ValueError("prover_statement lean_statement must be non-empty when result=ok")

    return result, lean_statement.strip(), notes.strip()


def validate_formalizer_output(payload: dict[str, Any], expected_problem_id: str) -> tuple[str, str, str, str]:
    required_keys = {"problem_id", "result", "proof_sketch", "proof_text", "counterexample_text"}
    if set(payload.keys()) != required_keys:
        raise ValueError("formalizer output keys mismatch required contract")

    problem_id = payload.get("problem_id")
    if problem_id != expected_problem_id:
        raise ValueError("formalizer output problem_id does not match picked problem")

    result = payload.get("result")
    if result not in {"proof", "counterexample", "stuck"}:
        raise ValueError("formalizer result must be one of: proof, counterexample, stuck")

    proof_sketch = payload.get("proof_sketch")
    proof_text = payload.get("proof_text")
    counterexample_text = payload.get("counterexample_text")
    if not isinstance(proof_sketch, str) or not isinstance(proof_text, str) or not isinstance(counterexample_text, str):
        raise ValueError("formalizer proof_sketch, proof_text and counterexample_text must be strings")

    return result, proof_sketch, proof_text, counterexample_text


def validate_expand_output(payload: dict[str, Any], expected_problem_id: str) -> list[dict[str, str]]:
    required_keys = {"problem_id", "candidates"}
    if set(payload.keys()) != required_keys:
        raise ValueError("expand output must contain exactly: problem_id, candidates")

    problem_id = payload.get("problem_id")
    if problem_id != expected_problem_id:
        raise ValueError("expand output problem_id does not match picked problem")

    candidates_value = payload.get("candidates")
    if not isinstance(candidates_value, list):
        raise ValueError("expand candidates must be an array of objects")
    if len(candidates_value) > 2:
        raise ValueError("expand candidates must have length <= 2")

    parsed: list[dict[str, str]] = []
    seen_norms: set[str] = set()
    for item in candidates_value:
        if not isinstance(item, dict) or set(item.keys()) != {"statement", "rationale"}:
            raise ValueError("each expand candidate must contain exactly: statement, rationale")
        statement = item.get("statement")
        rationale = item.get("rationale")
        if not isinstance(statement, str) or not isinstance(rationale, str):
            raise ValueError("expand candidate statement and rationale must be strings")
        normalized_statement = statement.strip()
        if not normalized_statement:
            continue
        norm = normalize_stmt_text(normalized_statement)
        if norm in seen_norms:
            continue
        seen_norms.add(norm)
        parsed.append({"statement": normalized_statement, "rationale": rationale.strip()})

    return parsed[:2]


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


def append_current_iteration_log(
    current_iteration_full_logs: list[dict[str, Any]],
    *,
    stage: str,
    index: int,
    worker_meta: dict[str, Any],
) -> None:
    raw_model_output = worker_meta.get("raw_model_output")
    if not isinstance(raw_model_output, str) or not raw_model_output.strip():
        return
    current_iteration_full_logs.append(
        {
            "stage": stage,
            "index": index,
            "raw_model_output": raw_model_output,
        }
    )


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


def extract_derived_theorem_entries(
    derived_path: Path,
    max_theorems: int = 50,
) -> list[dict[str, Any]]:
    """Extract theorem entries directly from Derived.lean."""
    fallback_entries = build_derived_entries_from_file(derived_path, max_theorems=max_theorems)
    return [
        {
            "name": str(entry.get("theorem_name", "")).strip(),
            "statement": str(entry.get("statement", "")).strip(),
            "alias_names": [str(value).strip() for value in entry.get("alias_names", []) if str(value).strip()],
        }
        for entry in fallback_entries[:max_theorems]
        if str(entry.get("theorem_name", "")).strip() and str(entry.get("statement", "")).strip()
    ]


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


def extract_entry_relevance_keywords(entry: dict[str, Any]) -> set[str]:
    keywords = set(extract_relevance_keywords(str(entry.get("statement", ""))))
    for item in entry.get("alias_names", []):
        keywords |= extract_relevance_keywords(str(item).replace("_", " "))
    keywords |= extract_relevance_keywords(str(entry.get("name", "")).replace("_", " "))
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
    entries: list[dict[str, Any]],
    stmt: str,
    max_entries: int = 5,
) -> list[dict[str, Any]]:
    if not entries:
        return []

    target_norm = normalize_stmt_text(stmt)
    target_shape = classify_statement_shape(stmt)
    target_keywords = extract_relevance_keywords(stmt)
    shortlisted: list[dict[str, Any]] = []
    seen_names: set[str] = set()

    def add_pass(predicate: Callable[[dict[str, Any]], bool]) -> None:
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

    def entry_shape(entry: dict[str, Any]) -> dict[str, bool]:
        return classify_statement_shape(entry["statement"])

    add_pass(
        lambda entry: same_relevance_family(target_shape, entry_shape(entry))
        and bool(target_keywords & extract_entry_relevance_keywords(entry))
    )
    add_pass(lambda entry: same_relevance_family(target_shape, entry_shape(entry)))
    add_pass(
        lambda entry: target_shape["has_exists"] == entry_shape(entry)["has_exists"]
        and target_shape["has_negation"] == entry_shape(entry)["has_negation"]
        and target_shape["has_mul"] == entry_shape(entry)["has_mul"]
    )
    return shortlisted[:max_entries]


def render_relevant_derived_context(entries: list[dict[str, Any]], max_chars: int = 1800) -> str:
    if not entries:
        return ""

    lines = [
        "",
        "-- Relevant verified theorems from Derived.lean:",
        "-- Check these theorem names before re-deriving from axioms.",
    ]
    for entry in entries:
        lines.append(f"-- {entry['name']} :: {summarize_derived_statement(entry['statement'])}")
        alias_names = [str(item).strip() for item in entry.get("alias_names", []) if str(item).strip()]
        if alias_names:
            lines.append(f"--   aliases: {', '.join(alias_names[:3])}")

    summary = "\n".join(lines)
    if len(summary) > max_chars:
        summary = summary[:max_chars] + "\n-- (relevant theorem list truncated)"
    return summary


def infer_mathlib_search_terms(stmt: str, entries: list[dict[str, Any]], max_terms: int = 10) -> list[str]:
    target_shape = classify_statement_shape(stmt)
    terms: list[str] = []

    def add(term: str) -> None:
        cleaned = term.strip()
        if not cleaned or cleaned in terms:
            return
        terms.append(cleaned)

    for keyword in sorted(extract_relevance_keywords(stmt)):
        add(keyword)

    if target_shape["has_subsingleton"]:
        add("Subsingleton")
        add("Subsingleton.elim")
    if target_shape["has_exists"]:
        add("Exists")
        add("Classical.choose")
    if target_shape["has_negation"]:
        add("False")
        add("by_contra")
    if target_shape["has_mul"]:
        add("mul")
    if target_shape["has_eq"]:
        add("Eq")
    if target_shape["has_forall"]:
        add("forall")
    for entry in entries:
        for alias_name in entry.get("alias_names", []):
            add(str(alias_name))
        add(str(entry.get("name", "")))

    return terms[:max_terms]


def infer_tactic_hints(stmt: str, entries: list[dict[str, Any]], max_tactics: int = 8) -> list[str]:
    target_shape = classify_statement_shape(stmt)
    tactics: list[str] = []

    def add(tactic: str) -> None:
        cleaned = tactic.strip()
        if not cleaned or cleaned in tactics:
            return
        tactics.append(cleaned)

    for tactic in ["simpa", "exact", "rw", "apply", "have", "calc"]:
        add(tactic)

    if target_shape["has_forall"]:
        add("intro")
    if target_shape["has_exists"]:
        add("refine")
        add("constructor")
        add("use")
        add("rcases")
    if target_shape["has_negation"]:
        add("intro")
        add("exfalso")
    if target_shape["has_subsingleton"]:
        add("Subsingleton.elim")
    if target_shape["has_eq"] and target_shape["has_mul"]:
        add("simp only")
    for entry in entries:
        if entry.get("name"):
            add(f"simpa using {entry['name']}")

    for tactic in ["aesop", "grind", "omega", "linarith", "nlinarith", "ring_nf", "positivity"]:
        add(tactic)

    return tactics[:max_tactics]


def render_mathlib_hint_context(stmt: str, entries: list[dict[str, Any]], max_chars: int = 900) -> str:
    search_terms = infer_mathlib_search_terms(stmt, entries)
    tactic_hints = infer_tactic_hints(stmt, entries)
    if not search_terms and not tactic_hints:
        return ""

    lines = [
        "",
        "-- Mathlib reuse hints:",
    ]
    if search_terms:
        lines.append(f"-- search keywords: {', '.join(search_terms)}")
    if tactic_hints:
        lines.append(f"-- tactic candidates: {', '.join(tactic_hints)}")
    lines.append("-- Prefer a short proof using existing Mathlib or Derived facts over axiom-only reconstruction.")

    summary = "\n".join(lines)
    if len(summary) > max_chars:
        summary = summary[:max_chars] + "\n-- (mathlib hints truncated)"
    return summary


def build_problem_theory_context(
    theory_context: str,
    derived_path: Path,
    stmt: str,
) -> str:
    entries = extract_derived_theorem_entries(derived_path)
    relevant_entries = shortlist_relevant_derived_entries(entries, stmt)
    relevant_summary = render_relevant_derived_context(relevant_entries)
    mathlib_summary = render_mathlib_hint_context(stmt, relevant_entries)
    context = theory_context
    if relevant_summary:
        context += relevant_summary
    if mathlib_summary:
        context += mathlib_summary
    return context


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
                "stage": str(item.get("stage", "")),
                "source_statement": str(item.get("source_statement", "")),
                "formalized_statement": str(item.get("formalized_statement", "")),
                "statement_formalization_notes": str(item.get("statement_formalization_notes", "")),
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


def append_formalization_memory_entry(
    memory_path: Path,
    problem_id: str,
    entry: dict[str, Any],
) -> list[dict[str, Any]]:
    history = load_formalization_memory(memory_path, problem_id)
    history.append(entry)
    if len(history) > 20:
        history = history[-20:]
    save_formalization_memory(memory_path, problem_id, history)
    return history


def query_prover_with_retries(
    worker_settings: Any,
    prover_prompt: str,
    problem_id: str,
    stmt: str,
    original_stmt: str,
    open_rows: list[dict[str, Any]],
    prover_retries: int,
    theory_context: str,
    memory_path: Path,
    current_iteration_full_logs: list[dict[str, Any]],
    same_problem_history_tail: list[dict[str, Any]],
) -> tuple[str, str, str, list[str], int, dict[str, Any]]:
    retries = max(1, prover_retries)
    last_result = "stuck"
    last_proof_sketch = ""
    last_counterexample_text = ""
    last_new_problems: list[str] = []
    last_worker_meta: dict[str, Any] = {}

    for attempt in range(1, retries + 1):
        payload: dict[str, Any] = {
            "problem_id": problem_id,
            "stmt": stmt,
            "original_stmt": original_stmt,
            "theory_context": theory_context,
            "open_problems": open_rows,
            "same_problem_history_tail": same_problem_history_tail,
            "prover_attempt_index": attempt,
            "prover_attempt_budget": retries,
            "mathlib_allowed": True,
            "new_problem_generation_policy": {
                "prefer_subgoals_when_stuck": True,
                "avoid_generalization_when_stuck": True,
                "prefer_intermediate_lemmas": True,
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
            append_current_iteration_log(
                current_iteration_full_logs,
                stage="prover",
                index=attempt,
                worker_meta=worker_meta,
            )
            prover_elapsed = time.monotonic() - prover_start
            debug_log(f"Prover returned for {problem_id}: {prover_payload.get('result', 'unknown')} (took {prover_elapsed:.1f}s)")
        except RuntimeError as exc:
            if is_worker_timeout_error(exc):
                debug_log(f"Prover timed out for {problem_id}: {exc}")
                timeout_sketch = (
                    "Prover worker timed out before returning a valid response. "
                    "Treating this iteration as stuck so the problem remains open. "
                    f"Details: {exc}"
                )
                timeout_subgoals = make_timeout_subgoals(
                    stmt=stmt,
                    memory_path=memory_path,
                    problem_id=problem_id,
                    fallback_candidates=last_new_problems,
                )
                return "stuck", timeout_sketch, "", timeout_subgoals, attempt, last_worker_meta
            raise
        result, proof_sketch, counterexample_text, new_problems = validate_prover_output(prover_payload, problem_id)

        last_result = result
        last_proof_sketch = proof_sketch
        last_counterexample_text = counterexample_text
        last_new_problems = new_problems

        if result != "stuck":
            return result, proof_sketch, counterexample_text, new_problems, attempt, last_worker_meta

    return (
        last_result,
        last_proof_sketch,
        last_counterexample_text,
        last_new_problems,
        retries,
        last_worker_meta,
    )


def request_initial_formalization(
    *,
    formalize_worker_settings: Any,
    formalizer_prompt: str,
    problem_id: str,
    stmt: str,
    result: str,
    proof_sketch: str,
    counterexample_text: str,
    open_rows: list[dict[str, Any]],
    theory_context: str,
    current_iteration_full_logs: list[dict[str, Any]],
    same_problem_history_tail: list[dict[str, Any]],
) -> tuple[str, str, str, str]:
    formalize_payload: dict[str, Any] = {
        "problem_id": problem_id,
        "stmt": stmt,
        "result": result,
        "proof_sketch": proof_sketch,
        "counterexample_text": counterexample_text,
        "theory_context": theory_context,
        "open_problems": open_rows,
        "same_problem_history_tail": same_problem_history_tail,
        "mathlib_allowed": True,
    }
    formalized, formalize_worker_meta = invoke_worker_json(
        settings=formalize_worker_settings,
        task_type="formalize",
        system_prompt=formalizer_prompt,
        payload=formalize_payload,
        metadata={"problem_id": problem_id},
    )
    append_current_iteration_log(
        current_iteration_full_logs,
        stage="formalize",
        index=1,
        worker_meta=formalize_worker_meta,
    )
    return validate_formalizer_output(formalized, problem_id)


def request_prover_statement_formalization(
    *,
    worker_settings: Any,
    prover_statement_prompt: str,
    problem_id: str,
    stmt: str,
    open_rows: list[dict[str, Any]],
    theory_context: str,
    current_iteration_full_logs: list[dict[str, Any]],
    same_problem_history_tail: list[dict[str, Any]],
) -> tuple[str, str, str, dict[str, Any]]:
    statement_payload: dict[str, Any] = {
        "problem_id": problem_id,
        "stmt": stmt,
        "theory_context": theory_context,
        "open_problems": open_rows,
        "same_problem_history_tail": same_problem_history_tail,
        "mathlib_allowed": True,
    }
    formalized, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="prover_statement",
        system_prompt=prover_statement_prompt,
        payload=statement_payload,
        metadata={"problem_id": problem_id},
    )
    append_current_iteration_log(
        current_iteration_full_logs,
        stage="prover_statement",
        index=1,
        worker_meta=worker_meta,
    )
    result, lean_statement, notes = validate_prover_statement_output(formalized, problem_id)
    return result, lean_statement, notes, worker_meta


def request_expand_candidates(
    *,
    worker_settings: Any,
    expand_prompt: str,
    problem_id: str,
    stmt: str,
    original_stmt: str,
    result: str,
    verify_success: bool,
    theory_context: str,
    existing_new_problems: list[str],
    verify_error_excerpt: str,
    current_iteration_full_logs: list[dict[str, Any]],
    same_problem_history_tail: list[dict[str, Any]],
) -> tuple[list[dict[str, str]], dict[str, Any]]:
    expand_payload: dict[str, Any] = {
        "problem_id": problem_id,
        "stmt": stmt,
        "original_stmt": original_stmt,
        "result": result,
        "verify_success": verify_success,
        "theory_context": theory_context,
        "existing_new_problems": list(existing_new_problems),
        "verify_error_excerpt": verify_error_excerpt,
        "current_iteration_full_logs": list(current_iteration_full_logs),
        "same_problem_history_tail": same_problem_history_tail,
        "expand_generation_policy": {
            "prefer_subgoals_for_unsolved": True,
            "avoid_generalization_for_unsolved": True,
            "prefer_same_problem_decomposition": True,
            "prefer_intermediate_lemmas": True,
        },
    }
    expanded, expand_worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="expand",
        system_prompt=expand_prompt,
        payload=expand_payload,
        metadata={"problem_id": problem_id},
    )
    append_current_iteration_log(
        current_iteration_full_logs,
        stage="expand",
        index=1,
        worker_meta=expand_worker_meta,
    )
    return validate_expand_output(expanded, problem_id), expand_worker_meta


def attempt_formalization_until_timeout(
    *,
    problem_id: str,
    stmt: str,
    result: str,
    proof_sketch: str,
    counterexample_text: str,
    new_problems: list[str],
    scratch_file: Path,
    skip_verify: bool,
    formalize_worker_settings: Any,
    repair_worker_settings: Any,
    formalizer_prompt: str,
    repair_prompt: str,
    open_rows: list[dict[str, Any]],
    theory_context: str,
    verify_timeout_sec: int = 180,
    formalization_retry_budget_sec: int,
    memory_path: Path,
    natural_language_note_markdown: str,
    natural_language_note_path: str,
    current_iteration_full_logs: list[dict[str, Any]],
    initial_proof_text: str = "",
    phase_logger: Callable[..., None] | None = None,
) -> tuple[bool, str | None, str, str, str, list[str], str]:
    verify_success = False
    theorem_name: str | None = None
    verify_error_excerpt = ""
    include_mathlib_import = False
    retained_new_problems = list(new_problems)
    proof_text = initial_proof_text

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

    if not proof_text.strip():
        if formalize_worker_settings is None:
            persisted_history = load_formalization_memory(memory_path, problem_id)
            persisted_history.append(
                {
                    "result": result,
                    "verify_success": verify_success,
                    "proof_sketch": proof_sketch,
                    "proof_text": proof_text,
                    "counterexample_text": counterexample_text,
                    "lean_error_excerpt": verify_error_excerpt,
                    "lean_error_fingerprint": "formalizer_unavailable",
                    "new_problems": list(new_problems)[:2],
                }
            )
            save_formalization_memory(memory_path, problem_id, persisted_history)
            return verify_success, theorem_name, "stuck", proof_text, counterexample_text, new_problems, verify_error_excerpt

        try:
            same_problem_history_tail = load_formalization_memory(memory_path, problem_id)[-8:]
            result, proof_sketch, proof_text, counterexample_text = request_initial_formalization(
                formalize_worker_settings=formalize_worker_settings,
                formalizer_prompt=formalizer_prompt,
                problem_id=problem_id,
                stmt=stmt,
                result=result,
                proof_sketch=proof_sketch,
                counterexample_text=counterexample_text,
                open_rows=open_rows,
                theory_context=theory_context,
                current_iteration_full_logs=current_iteration_full_logs,
                same_problem_history_tail=same_problem_history_tail,
            )
        except RuntimeError as exc:
            if is_worker_timeout_error(exc):
                persisted_history = load_formalization_memory(memory_path, problem_id)
                verify_error_excerpt = f"formalize worker timeout: {exc}"
                persisted_history.append(
                    {
                        "result": "stuck",
                        "verify_success": verify_success,
                        "proof_sketch": proof_sketch,
                        "proof_text": proof_text,
                        "counterexample_text": counterexample_text,
                        "lean_error_excerpt": verify_error_excerpt,
                        "lean_error_fingerprint": "formalizer_timeout",
                        "new_problems": list(new_problems)[:2],
                    }
                )
                save_formalization_memory(memory_path, problem_id, persisted_history)
                return verify_success, theorem_name, "stuck", proof_text, counterexample_text, new_problems, verify_error_excerpt
            raise
        if result not in {"proof", "counterexample"}:
            persisted_history = load_formalization_memory(memory_path, problem_id)
            persisted_history.append(
                {
                    "result": result,
                    "verify_success": verify_success,
                    "proof_sketch": proof_sketch,
                    "proof_text": proof_text,
                    "counterexample_text": counterexample_text,
                    "lean_error_excerpt": verify_error_excerpt,
                    "lean_error_fingerprint": "formalizer_returned_stuck",
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

        if repair_worker_settings is None or time.monotonic() >= deadline:
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
            "prover_attempt_index": repair_round,
            "prover_attempt_budget": "until_formalization_timeout",
            "mathlib_allowed": True,
            "new_problem_generation_policy": {
                "prefer_subgoals_when_stuck": True,
                "avoid_generalization_when_stuck": True,
                "prefer_intermediate_lemmas": True,
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
            repaired, repair_worker_meta = invoke_worker_json(
                settings=repair_worker_settings,
                task_type="repair",
                system_prompt=repair_prompt,
                payload=repair_payload,
                metadata={"problem_id": problem_id, "repair_round": repair_round},
            )
            append_current_iteration_log(
                current_iteration_full_logs,
                stage="repair",
                index=repair_round,
                worker_meta=repair_worker_meta,
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
            result, proof_sketch, proof_text, counterexample_text = validate_formalizer_output(repaired, problem_id)
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
    proof_notes_dir: Path,
    reset_proof_notes: bool,
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

    if reset_proof_notes:
        shutil.rmtree(proof_notes_dir, ignore_errors=True)
        proof_notes_dir.mkdir(parents=True, exist_ok=True)

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
    parser = argparse.ArgumentParser(description="Run the minimal prototype loop.")
    parser.add_argument("--initialize-on-start", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--enable-worker", action="store_true")
    parser.add_argument("--worker-command")
    parser.add_argument("--worker-timeout", type=int)
    parser.add_argument("--prover-statement-worker-command")
    parser.add_argument("--prover-statement-worker-timeout", type=int)
    parser.add_argument("--formalize-worker-command")
    parser.add_argument("--formalize-worker-timeout", type=int)
    parser.add_argument("--repair-worker-command")
    parser.add_argument("--repair-worker-timeout", type=int)
    parser.add_argument("--prover-statement-prompt-file", default="prompts/prover_statement_formalizer.md")
    parser.add_argument("--formalizer-prompt-file", default="prompts/formalizer_simple.md")
    parser.add_argument("--repair-prompt-file")
    parser.add_argument("--phase-logs", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--skip-verify", action="store_true")
    args = parser.parse_args()

    # Fixed runtime paths and hidden compatibility defaults.
    args.data_dir = "data"
    args.seeds_file = "theories/semigroup_like_01/seeds.jsonl"
    args.scratch_file = "AutomatedTheoryConstruction/Scratch.lean"
    args.derived_file = "AutomatedTheoryConstruction/Derived.lean"
    args.proof_notes_dir = "data/proof_notes"
    args.reset_proof_notes_on_start = True
    args.reset_scratch_on_start = True
    args.reset_derived_on_start = True
    args.prover_output_json = None
    args.prover_output_file = None
    args.theory_file = "AutomatedTheoryConstruction/Theory.lean"
    # Problem selection is deterministic local logic; the worker handles prover_statement/prover/formalize/repair/expand.
    args.prover_prompt_file = "prompts/prover_simple.md"
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
    scratch_file = Path(args.scratch_file)
    memory_path = Path(args.formalization_memory_file)
    proof_notes_dir = Path(args.proof_notes_dir)

    if args.initialize_on_start:
        initialize_runtime_state(
            data_dir=data_dir,
            seeds_file=Path(args.seeds_file),
            proof_notes_dir=proof_notes_dir,
            reset_proof_notes=args.reset_proof_notes_on_start,
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

    base_theory_context = load_optional_text(args.theory_file)
    derived_path = Path(args.derived_file)
    open_path = data_dir / "open_problems.jsonl"

    worker_settings = None
    prover_statement_worker_settings = None
    formalize_worker_settings = None
    repair_worker_settings = None
    if args.enable_worker:
        worker_settings = load_worker_settings(
            command_override=args.worker_command,
            timeout_override=args.worker_timeout,
        )
        prover_statement_worker_settings = load_task_worker_settings(
            task_name="prover_statement",
            base_settings=worker_settings,
            command_override=args.prover_statement_worker_command,
            timeout_override=args.prover_statement_worker_timeout,
        )
        formalize_worker_settings = load_task_worker_settings(
            task_name="formalize",
            base_settings=worker_settings,
            command_override=args.formalize_worker_command,
            timeout_override=args.formalize_worker_timeout,
        )
        repair_worker_settings = load_task_worker_settings(
            task_name="repair",
            base_settings=worker_settings,
            command_override=args.repair_worker_command,
            timeout_override=args.repair_worker_timeout,
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

        iteration_num = completed_iterations + 1
        debug_log(f"=== Iteration {iteration_num} START ===")
        debug_log(f"{len(open_rows)} total problems in queue")

        emit_phase_log(
            args.phase_logs,
            "iteration_start",
            iteration=completed_iterations + 1,
            open_problem_count=len(open_rows),
        )

        # Select problem using local deterministic logic, no LLM needed
        debug_log(f"Selecting problem locally from {len(open_rows)} queued problems")
        picked = pick_next_problem(open_rows)

        if picked is None:
            print({"status": "no_open_problems", "iterations_completed": completed_iterations})
            return

        problem_id = str(picked["id"])
        original_stmt = str(picked.get("stmt", ""))
        initial_theory_context = build_problem_theory_context(base_theory_context, derived_path, original_stmt)
        emit_phase_log(args.phase_logs, "problem_selected", iteration=completed_iterations + 1, problem_id=problem_id)

        current_iteration_full_logs: list[dict[str, Any]] = []
        solver_stmt = original_stmt if looks_formalizable(original_stmt) else ""
        statement_formalization_result = "ok" if solver_stmt else "stuck"
        statement_formalization_notes = (
            "Using the existing statement directly."
            if solver_stmt
            else "Original statement is not obviously Lean-formalizable."
        )
        prover_statement_worker_meta: dict[str, Any] = {}
        same_problem_history_tail = load_formalization_memory(memory_path, problem_id)[-8:]

        if prover_statement_worker_settings is not None:
            emit_phase_log(
                args.phase_logs,
                "prover_statement",
                iteration=completed_iterations + 1,
                problem_id=problem_id,
                mode="worker",
            )
            prover_statement_prompt = load_prompt_text(args.prover_statement_prompt_file)
            try:
                (
                    statement_formalization_result,
                    formalized_stmt,
                    statement_formalization_notes,
                    prover_statement_worker_meta,
                ) = request_prover_statement_formalization(
                    worker_settings=prover_statement_worker_settings,
                    prover_statement_prompt=prover_statement_prompt,
                    problem_id=problem_id,
                    stmt=original_stmt,
                    open_rows=open_rows,
                    theory_context=initial_theory_context,
                    current_iteration_full_logs=current_iteration_full_logs,
                    same_problem_history_tail=same_problem_history_tail,
                )
            except RuntimeError as exc:
                if is_worker_timeout_error(exc):
                    statement_formalization_result = "stuck"
                    formalized_stmt = ""
                    statement_formalization_notes = f"prover_statement worker timeout: {exc}"
                else:
                    raise
            else:
                emit_phase_log(
                    args.phase_logs,
                    "prover_statement_parse",
                    iteration=completed_iterations + 1,
                    problem_id=problem_id,
                    json_parse_attempts=int(prover_statement_worker_meta.get("json_parse_attempts", 0) or 0),
                    raw_parse_fallback_used=bool(prover_statement_worker_meta.get("raw_parse_fallback_used", False)),
                    client_json_parse_attempts=int(prover_statement_worker_meta.get("client_json_parse_attempts", 0) or 0),
                    client_raw_parse_fallback_used=bool(prover_statement_worker_meta.get("client_raw_parse_fallback_used", False)),
                )
            if statement_formalization_result == "ok":
                solver_stmt = formalized_stmt
            elif solver_stmt:
                statement_formalization_result = "ok"
                statement_formalization_notes = (
                    f"{statement_formalization_notes} Falling back to the existing statement because it already looks Lean-formalizable."
                ).strip()
            else:
                solver_stmt = ""
            emit_phase_log(
                args.phase_logs,
                "prover_statement_result",
                iteration=completed_iterations + 1,
                problem_id=problem_id,
                formalized=statement_formalization_result == "ok",
                notes=statement_formalization_notes,
            )

        append_formalization_memory_entry(
            memory_path,
            problem_id,
            {
                "stage": "statement_formalization",
                "source_statement": original_stmt,
                "formalized_statement": solver_stmt,
                "statement_formalization_notes": statement_formalization_notes,
                "result": statement_formalization_result,
                "verify_success": statement_formalization_result == "ok" and bool(solver_stmt),
                "proof_sketch": "",
                "proof_text": "",
                "counterexample_text": "",
                "lean_error_excerpt": "",
                "lean_error_fingerprint": "statement_formalization",
                "new_problems": [],
            },
        )
        same_problem_history_tail = load_formalization_memory(memory_path, problem_id)[-8:]

        theory_context = build_problem_theory_context(
            base_theory_context,
            derived_path,
            solver_stmt if solver_stmt else original_stmt,
        )

        prover_payload = load_json_payload_from_args(args.prover_output_json, args.prover_output_file)
        prover_attempts_used = 1
        proof_sketch = ""
        proof_text = ""
        counterexample_text = ""
        prover_worker_meta: dict[str, Any] = {}
        new_problems: list[str] = []
        if statement_formalization_result != "ok" or not solver_stmt:
            result = "stuck"
            proof_sketch = statement_formalization_notes or "Statement formalization failed before proof search."
            counterexample_text = ""
            new_problems = []
        elif prover_payload is not None:
            emit_phase_log(args.phase_logs, "prover", iteration=completed_iterations + 1, problem_id=problem_id, mode="provided")
            result, proof_sketch, counterexample_text, new_problems = validate_prover_output(prover_payload, problem_id)
        elif worker_settings is not None:
            emit_phase_log(args.phase_logs, "prover", iteration=completed_iterations + 1, problem_id=problem_id, mode="worker")
            prover_prompt = load_prompt_text(args.prover_prompt_file)
            result, proof_sketch, counterexample_text, new_problems, prover_attempts_used, prover_worker_meta = query_prover_with_retries(
                worker_settings=worker_settings,
                prover_prompt=prover_prompt,
                problem_id=problem_id,
                stmt=solver_stmt,
                original_stmt=original_stmt,
                open_rows=open_rows,
                prover_retries=args.prover_retries,
                theory_context=theory_context,
                memory_path=memory_path,
                current_iteration_full_logs=current_iteration_full_logs,
                same_problem_history_tail=same_problem_history_tail,
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
            counterexample_text = args.mock_counterexample_text
            proof_text = args.mock_proof_text
            new_problems = parse_new_problems(args.mock_new_problem)

        note_path, note_markdown = write_proof_note_markdown(
            proof_notes_dir,
            problem_id=problem_id,
            stmt=solver_stmt if solver_stmt else original_stmt,
            result=result,
            proof_sketch=proof_sketch,
            counterexample_text=counterexample_text,
        )

        formalizer_prompt = load_prompt_text(args.formalizer_prompt_file) if formalize_worker_settings is not None else ""
        repair_prompt_file = args.repair_prompt_file or args.formalizer_prompt_file
        repair_prompt = load_prompt_text(repair_prompt_file) if repair_worker_settings is not None else ""
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
            stmt=solver_stmt if solver_stmt else original_stmt,
            result=result,
            proof_sketch=proof_sketch,
            counterexample_text=counterexample_text,
            new_problems=new_problems,
            scratch_file=scratch_file,
            skip_verify=args.skip_verify,
            formalize_worker_settings=formalize_worker_settings,
            repair_worker_settings=repair_worker_settings,
            formalizer_prompt=formalizer_prompt,
            repair_prompt=repair_prompt,
            open_rows=open_rows,
            theory_context=theory_context,
            verify_timeout_sec=180,
            formalization_retry_budget_sec=args.formalization_retry_budget_sec,
            memory_path=memory_path,
            natural_language_note_markdown=note_markdown,
            natural_language_note_path=str(note_path),
            current_iteration_full_logs=current_iteration_full_logs,
            initial_proof_text=proof_text,
            phase_logger=(lambda **fields: emit_phase_log(args.phase_logs, iteration=completed_iterations + 1, **fields)),
        )
        if verify_success and result in {"proof", "counterexample"}:
            scratch_code = scratch_file.read_text(encoding="utf-8")
            theorem_body_match = re.search(
                r"namespace AutomatedTheoryConstruction\n\n(.*)\nend AutomatedTheoryConstruction",
                scratch_code,
                re.DOTALL,
            )
            if theorem_body_match:
                # Append the newly verified theorem before expansion so follow-up
                # generation can immediately reuse the latest derived facts.
                append_theorem(
                    Path(args.derived_file),
                    theorem_body_match.group(1),
                    None,
                )
                theory_context = build_problem_theory_context(base_theory_context, derived_path, solver_stmt)

        solver_new_problem_suggestions = list(new_problems)
        expander_new_problem_suggestions: list[str] = []
        expander_worker_meta: dict[str, Any] = {}
        expand_target_stmt = solver_stmt if solver_stmt else original_stmt

        new_problems = list(solver_new_problem_suggestions)

        if worker_settings is not None:
            emit_phase_log(
                args.phase_logs,
                "expand_generate",
                iteration=completed_iterations + 1,
                problem_id=problem_id,
                mode="worker",
            )
            expand_prompt = load_prompt_text(args.expander_prompt_file)
            same_problem_history_tail = load_formalization_memory(memory_path, problem_id)[-8:]
            try:
                expander_candidates, expander_worker_meta = request_expand_candidates(
                    worker_settings=worker_settings,
                    expand_prompt=expand_prompt,
                    problem_id=problem_id,
                    stmt=expand_target_stmt,
                    original_stmt=original_stmt,
                    result=result,
                    verify_success=verify_success,
                    theory_context=theory_context,
                    existing_new_problems=solver_new_problem_suggestions,
                    verify_error_excerpt=verify_error_excerpt,
                    current_iteration_full_logs=current_iteration_full_logs,
                    same_problem_history_tail=same_problem_history_tail,
                )
                emit_phase_log(
                    args.phase_logs,
                    "expand_generate_result",
                    iteration=completed_iterations + 1,
                    problem_id=problem_id,
                    generated_count=len(expander_candidates),
                )
                expander_new_problem_suggestions = [item["statement"] for item in expander_candidates]
                new_problems = merge_new_problems(new_problems, expander_new_problem_suggestions)
            except (RuntimeError, ValueError) as exc:
                debug_log(f"Expander failed for {problem_id}: {exc}")
                emit_phase_log(
                    args.phase_logs,
                    "expand_generate_error",
                    iteration=completed_iterations + 1,
                    problem_id=problem_id,
                    error=str(exc),
                )

        report = apply_state_update(
            data_dir=data_dir,
            problem_id=problem_id,
            result=result,
            verify_success=verify_success,
            theorem_name=theorem_name,
            new_problems=new_problems,
        )
        emit_phase_log(args.phase_logs, "state_update", iteration=completed_iterations + 1, problem_id=problem_id)
        completed_iterations += 1
        debug_log(f"=== Iteration {completed_iterations} END ({result}, verify={verify_success}) ===\n")
        report["picked_problem_id"] = problem_id
        report["result"] = result
        report["verify_success"] = verify_success
        report["verify_error_excerpt"] = verify_error_excerpt
        report["original_stmt"] = original_stmt
        report["formalized_stmt"] = solver_stmt
        report["prover_statement_result"] = statement_formalization_result
        report["prover_statement_notes"] = statement_formalization_notes
        report["prover_attempts_used"] = prover_attempts_used
        report["prover_proof_sketch"] = proof_sketch
        report["prover_counterexample_text"] = counterexample_text
        report["prover_new_problem_suggestions"] = solver_new_problem_suggestions
        report["expander_new_problem_suggestions"] = expander_new_problem_suggestions
        report["final_new_problems"] = new_problems
        report["proof_note_path"] = str(note_path)
        report["prover_statement_worker_json_parse_attempts"] = int(prover_statement_worker_meta.get("json_parse_attempts", 0) or 0)
        report["prover_statement_worker_raw_parse_fallback_used"] = bool(prover_statement_worker_meta.get("raw_parse_fallback_used", False))
        report["prover_statement_client_json_parse_attempts"] = int(prover_statement_worker_meta.get("client_json_parse_attempts", 0) or 0)
        report["prover_statement_client_raw_parse_fallback_used"] = bool(prover_statement_worker_meta.get("client_raw_parse_fallback_used", False))
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
