from __future__ import annotations

import json
import re
import sys
import threading
import time
from pathlib import Path
from typing import Any
from typing import Callable

from common import append_jsonl
from common import normalize_open_problem_priority
from guidance import build_guidance_context
from materials import DEFAULT_MATERIALS_DIR
from materials import load_materials
from materials_sync import ensure_materials_derived_current
from research_agenda import DEFAULT_RESEARCH_AGENDA_PATH
from research_agenda import load_research_agenda


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
THEORY_STATE_FILENAME = "theory_state.json"
THEOREM_NAME_STEM_PATTERN = re.compile(r"^[a-z][a-z0-9_]*$")
DERIVED_THEOREM_HEADER_PATTERN = re.compile(r"\btheorem\s+([A-Za-z0-9_']+)\s*:")
PHASE_ATTEMPT_LOCK = threading.Lock()
FORMALIZATION_MEMORY_LOCK = threading.RLock()


def debug_log(msg: str) -> None:
    timestamp = time.strftime("%H:%M:%S")
    print(f"[{timestamp}] {msg}", file=sys.stderr, flush=True)


def theory_state_path(data_dir: Path) -> Path:
    return data_dir / THEORY_STATE_FILENAME


def load_current_research_agenda() -> dict[str, Any]:
    return load_research_agenda(REPO_ROOT / DEFAULT_RESEARCH_AGENDA_PATH)


def load_current_materials() -> dict[str, Any]:
    ensure_materials_derived_current(REPO_ROOT / DEFAULT_MATERIALS_DIR)
    return load_materials(REPO_ROOT / DEFAULT_MATERIALS_DIR)


def load_theory_state(data_dir: Path) -> dict[str, Any]:
    path = theory_state_path(data_dir)
    if not path.exists():
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}
    return payload if isinstance(payload, dict) else {}


def load_current_guidance(data_dir: Path) -> dict[str, dict[str, Any]]:
    return build_guidance_context(
        theory_state=load_theory_state(data_dir),
        research_agenda=load_current_research_agenda(),
        materials=load_current_materials(),
    )


def append_phase_attempt_record(
    phase_attempts_path: Path | None,
    *,
    run_id: str,
    session_type: str,
    iteration: int,
    entity_id: str,
    phase: str,
    worker_task: str,
    started_at: str,
    finished_at: str,
    duration_ms: int,
    success: bool,
    result: str,
    timeout: bool = False,
    error: str = "",
) -> None:
    if phase_attempts_path is None:
        return
    with PHASE_ATTEMPT_LOCK:
        append_jsonl(
            phase_attempts_path,
            {
                "run_id": run_id,
                "session_type": session_type,
                "iteration": iteration,
                "entity_id": entity_id,
                "phase": phase,
                "worker_task": worker_task,
                "started_at": started_at,
                "finished_at": finished_at,
                "duration_ms": duration_ms,
                "success": bool(success),
                "result": result,
                "timeout": bool(timeout),
                "error": error,
            },
        )


def normalize_stmt_text(stmt: str) -> str:
    return " ".join(stmt.split())


def open_problem_priority_label(row: dict[str, Any]) -> str:
    return normalize_open_problem_priority(row.get("priority"))


def is_verified_resolution(*, verify_success: bool, result: str) -> bool:
    return bool(verify_success and result in {"proof", "counterexample"})


def validate_theorem_name_stem(stem: str) -> str:
    cleaned = stem.strip()
    if not cleaned:
        raise ValueError("prover_statement theorem_name_stem must be non-empty when result=ok")
    if len(cleaned) > 80:
        raise ValueError("prover_statement theorem_name_stem must be <= 80 characters")
    if not THEOREM_NAME_STEM_PATTERN.fullmatch(cleaned):
        raise ValueError("prover_statement theorem_name_stem must match ^[a-z][a-z0-9_]*$")
    if cleaned.startswith("thm_") or cleaned == "thm":
        raise ValueError("prover_statement theorem_name_stem must not include the thm prefix")
    if cleaned.startswith("_") or cleaned.endswith("_") or "__" in cleaned:
        raise ValueError("prover_statement theorem_name_stem must not have leading/trailing/repeated underscores")
    if re.search(r"_\d+$", cleaned):
        raise ValueError("prover_statement theorem_name_stem must not end with a numeric suffix")
    return cleaned


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
        candidate_statement = normalize_stmt_text(theorem_code[start:separator_index].strip())
        if candidate_statement:
            theorem_name = candidate_name
            statement = candidate_statement

    if not theorem_name or not statement:
        return None
    return {
        "name": theorem_name,
        "statement": statement,
    }


def append_derived_entry_cache(
    entries: list[dict[str, str]],
    theorem_code: str,
) -> None:
    entry = extract_derived_entry_from_theorem_code(theorem_code)
    if entry is None:
        return
    if any(existing["name"] == entry["name"] for existing in entries):
        return
    entries.append(entry)


def extract_theorem_code_from_scratch(scratch_path: Path) -> str:
    scratch_code = scratch_path.read_text(encoding="utf-8")
    namespace_match = re.search(
        r"namespace\s+AutomatedTheoryConstruction\b",
        scratch_code,
    )
    if namespace_match is None:
        debug_log(f"Could not find AutomatedTheoryConstruction namespace in {scratch_path}")
        return scratch_code.strip()
    namespace_tail = scratch_code[namespace_match.end() :]
    end_match = re.search(r"\nend\s+AutomatedTheoryConstruction", namespace_tail)
    if end_match is None:
        debug_log(f"Could not find namespace end marker in {scratch_path}")
        return namespace_tail.strip()
    return namespace_tail[: end_match.start()].strip()


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
        "-- Relevant verified theorems from Generated/Derived:",
        "-- Check these theorem names before re-deriving from axioms.",
    ]
    for entry in entries:
        lines.append(f"-- {entry['name']} :: {summarize_derived_statement(entry['statement'])}")

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
    derived_entries: list[dict[str, str]],
    stmt: str,
) -> str:
    relevant_entries = shortlist_relevant_derived_entries(derived_entries, stmt)
    relevant_summary = render_relevant_derived_context(relevant_entries)
    mathlib_summary = render_mathlib_hint_context(stmt, relevant_entries)
    context = theory_context
    if relevant_summary:
        context += relevant_summary
    if mathlib_summary:
        context += mathlib_summary
    return context


def load_formalization_memory(memory_path: Path, problem_id: str) -> list[dict[str, Any]]:
    with FORMALIZATION_MEMORY_LOCK:
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
                }
            )
        return safe_rows


def save_formalization_memory(memory_path: Path, problem_id: str, history: list[dict[str, Any]]) -> None:
    with FORMALIZATION_MEMORY_LOCK:
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
    with FORMALIZATION_MEMORY_LOCK:
        history = load_formalization_memory(memory_path, problem_id)
        history.append(entry)
        if len(history) > 20:
            history = history[-20:]
        save_formalization_memory(memory_path, problem_id, history)
        return history
