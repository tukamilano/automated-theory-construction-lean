from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import Any


def _as_str_list(value: Any) -> list[str]:
    if not isinstance(value, list):
        return []
    return [str(item).strip() for item in value if str(item).strip()]


def _coerce_text(value: Any) -> str:
    return str(value).strip()


def _coerce_bool_map(value: Any) -> dict[str, Any]:
    return dict(value) if isinstance(value, dict) else {}


def _coerce_rows(value: Any) -> list[dict[str, Any]]:
    if not isinstance(value, list):
        return []
    rows: list[dict[str, Any]] = []
    for item in value:
        if isinstance(item, dict):
            rows.append(item)
    return rows


@dataclass(frozen=True)
class ProverRequestPacket:
    problem_id: str
    stmt: str
    original_stmt: str
    derived_theorems: list[dict[str, str]]
    theory_context: str
    same_problem_history_tail: list[dict[str, Any]]
    retry_round: int = 0
    retry_instruction: str = ""
    previous_result: str = ""
    previous_proof_sketch: str = ""
    previous_counterexample_text: str = ""

    def to_payload(self) -> dict[str, Any]:
        payload: dict[str, Any] = {
            "problem_id": self.problem_id,
            "stmt": self.stmt,
            "original_stmt": self.original_stmt,
            "derived_theorems": self.derived_theorems,
            "theory_context": self.theory_context,
            "same_problem_history_tail": self.same_problem_history_tail,
            "retry_round": self.retry_round,
        }
        if self.retry_instruction:
            payload["retry_instruction"] = self.retry_instruction
        if self.previous_result:
            payload["previous_result"] = self.previous_result
        if self.previous_proof_sketch:
            payload["previous_proof_sketch"] = self.previous_proof_sketch
        if self.previous_counterexample_text:
            payload["previous_counterexample_text"] = self.previous_counterexample_text
        return payload


@dataclass(frozen=True)
class ProverResponsePacket:
    problem_id: str
    result: str
    proof_sketch: str
    counterexample_text: str
    new_problems: list[str] = field(default_factory=list)
    attempt: int = 0
    worker_meta: dict[str, Any] = field(default_factory=dict)
    raw_payload: dict[str, Any] = field(default_factory=dict)

    def with_attempt(self, attempt: int) -> "ProverResponsePacket":
        return replace(self, attempt=attempt)

    def with_worker_meta(self, worker_meta: dict[str, Any]) -> "ProverResponsePacket":
        return replace(self, worker_meta=worker_meta)

    def as_tuple(self) -> tuple[str, str, str, int, dict[str, Any]]:
        return (
            self.result,
            self.proof_sketch,
            self.counterexample_text,
            self.attempt,
            self.worker_meta,
        )


@dataclass(frozen=True)
class FormalizerRequestPacket:
    problem_id: str
    stmt: str
    result: str
    proof_sketch: str
    counterexample_text: str
    theory_context: str
    open_rows: list[dict[str, Any]]
    same_problem_history_tail: list[dict[str, Any]]
    mathlib_allowed: bool = True

    def to_payload(self) -> dict[str, Any]:
        return {
            "problem_id": self.problem_id,
            "stmt": self.stmt,
            "result": self.result,
            "proof_sketch": self.proof_sketch,
            "counterexample_text": self.counterexample_text,
            "theory_context": self.theory_context,
            "open_problems": self.open_rows,
            "same_problem_history_tail": self.same_problem_history_tail,
            "mathlib_allowed": self.mathlib_allowed,
        }


@dataclass(frozen=True)
class FormalizerResponsePacket:
    problem_id: str
    result: str
    proof_sketch: str
    prelude_code: str = ""
    proof_text: str = ""
    counterexample_text: str = ""
    raw_payload: dict[str, Any] = field(default_factory=dict)

    def as_tuple(self) -> tuple[str, str, str, str, str]:
        return (
            self.result,
            self.proof_sketch,
            self.prelude_code,
            self.proof_text,
            self.counterexample_text,
        )

    def to_prover_direction_tuple(self) -> tuple[str, str, str, str, str]:
        return (
            self.result,
            self.proof_sketch,
            self.proof_text,
            self.counterexample_text,
            "",
        )


@dataclass(frozen=True)
class SolverStatementRequestPacket:
    problem_id: str
    stmt: str
    theory_context: str
    open_rows: list[dict[str, Any]]
    repair_round: int = 0
    retry_instruction: str = ""
    previous_statement_prelude_code: str = ""
    previous_lean_statement: str = ""
    previous_theorem_name_stem: str = ""
    previous_docstring_summary: str = ""
    previous_notes: str = ""
    lean_error_excerpt: str = ""
    lean_error_top_lines: list[str] = field(default_factory=list)
    lean_diagnostics: str = ""
    repair_history_tail: list[dict[str, Any]] = field(default_factory=list)

    def to_payload(self) -> dict[str, Any]:
        payload: dict[str, Any] = {
            "problem_id": self.problem_id,
            "stmt": self.stmt,
            "theory_context": self.theory_context,
            "open_problems": self.open_rows,
            "repair_round": self.repair_round,
        }
        if self.retry_instruction:
            payload["retry_instruction"] = self.retry_instruction
        if self.previous_statement_prelude_code:
            payload["previous_statement_prelude_code"] = self.previous_statement_prelude_code
        if self.previous_lean_statement:
            payload["previous_lean_statement"] = self.previous_lean_statement
        if self.previous_theorem_name_stem:
            payload["previous_theorem_name_stem"] = self.previous_theorem_name_stem
        if self.previous_docstring_summary:
            payload["previous_docstring_summary"] = self.previous_docstring_summary
        if self.previous_notes:
            payload["previous_notes"] = self.previous_notes
        if self.lean_error_excerpt:
            payload["lean_error_excerpt"] = self.lean_error_excerpt
        if self.lean_error_top_lines:
            payload["lean_error_top_lines"] = list(self.lean_error_top_lines)
        if self.lean_diagnostics:
            payload["lean_diagnostics"] = self.lean_diagnostics
        if self.repair_history_tail:
            payload["repair_history_tail"] = list(self.repair_history_tail)
        return payload


@dataclass(frozen=True)
class RepairRequestPacket:
    problem_id: str
    stmt: str
    theory_context: str
    retry_instruction: str
    error_fingerprint: str
    error_categories: list[str]
    previous_result: str
    previous_proof_sketch: str
    previous_prelude_code: str
    previous_proof_text: str
    previous_counterexample_text: str
    repair_history_tail: list[dict[str, Any]]
    lean_error_excerpt: str
    lean_error_top_lines: list[str]
    lean_diagnostics: str
    current_scratch_code: str
    mathlib_import_in_scratch: bool = True
    new_problem_generation_policy: dict[str, Any] = field(
        default_factory=lambda: {
            "prefer_subgoals_when_stuck": True,
            "avoid_generalization_when_stuck": True,
            "prefer_intermediate_lemmas": True,
            "avoid_direct_axiom_instantiation": True,
            "avoid_variable_renaming_only": True,
            "target_novelty": "medium_or_high",
        }
    )

    def to_payload(self) -> dict[str, Any]:
        return {
            "problem_id": self.problem_id,
            "stmt": self.stmt,
            "theory_context": self.theory_context,
            "new_problem_generation_policy": self.new_problem_generation_policy,
            "retry_instruction": self.retry_instruction,
            "error_fingerprint": self.error_fingerprint,
            "error_categories": list(self.error_categories),
            "previous_result": self.previous_result,
            "previous_proof_sketch": self.previous_proof_sketch,
            "previous_prelude_code": self.previous_prelude_code,
            "previous_proof_text": self.previous_proof_text,
            "previous_counterexample_text": self.previous_counterexample_text,
            "repair_history_tail": list(self.repair_history_tail),
            "lean_error_excerpt": self.lean_error_excerpt,
            "lean_error_top_lines": list(self.lean_error_top_lines),
            "lean_diagnostics": self.lean_diagnostics,
            "current_scratch_code": self.current_scratch_code,
            "mathlib_import_in_scratch": self.mathlib_import_in_scratch,
        }


def normalize_prover_payload(payload: dict[str, Any], expected_problem_id: str) -> ProverResponsePacket:
    result = str(payload.get("result", "")).strip()
    proof_sketch = _coerce_text(payload.get("proof_sketch"))
    counterexample_text = _coerce_text(payload.get("counterexample_text"))
    new_problems = _as_str_list(payload.get("new_problems"))
    return ProverResponsePacket(
        problem_id=expected_problem_id,
        result=result,
        proof_sketch=proof_sketch,
        counterexample_text=counterexample_text,
        new_problems=new_problems,
        raw_payload=dict(payload),
    )


def normalize_formalizer_payload(payload: dict[str, Any], expected_problem_id: str) -> FormalizerResponsePacket:
    result = str(payload.get("result", "")).strip()
    proof_sketch = _coerce_text(payload.get("proof_sketch"))
    prelude_code = _coerce_text(payload.get("prelude_code"))
    proof_text = _coerce_text(payload.get("proof_text"))
    counterexample_text = _coerce_text(payload.get("counterexample_text"))
    return FormalizerResponsePacket(
        problem_id=expected_problem_id,
        result=result,
        proof_sketch=proof_sketch,
        prelude_code=prelude_code,
        proof_text=proof_text,
        counterexample_text=counterexample_text,
        raw_payload=dict(payload),
    )


def build_solver_statement_request_from_kwargs(**kwargs: Any) -> SolverStatementRequestPacket:
    return SolverStatementRequestPacket(
        problem_id=kwargs.get("problem_id", ""),
        stmt=kwargs.get("stmt", ""),
        theory_context=kwargs.get("theory_context", ""),
        open_rows=_coerce_rows(kwargs.get("open_rows", [])),
        repair_round=int(kwargs.get("repair_round", 0)),
        retry_instruction=kwargs.get("retry_instruction", "") or "",
        previous_statement_prelude_code=kwargs.get("previous_statement_prelude_code", "") or "",
        previous_lean_statement=kwargs.get("previous_lean_statement", "") or "",
        previous_theorem_name_stem=kwargs.get("previous_theorem_name_stem", "") or "",
        previous_docstring_summary=kwargs.get("previous_docstring_summary", "") or "",
        previous_notes=kwargs.get("previous_notes", "") or "",
        lean_error_excerpt=kwargs.get("lean_error_excerpt", "") or "",
        lean_error_top_lines=_as_str_list(kwargs.get("lean_error_top_lines", [])),
        lean_diagnostics=kwargs.get("lean_diagnostics", "") or "",
        repair_history_tail=_coerce_rows(kwargs.get("repair_history_tail", [])),
    )


def build_repair_request_from_state(**kwargs: Any) -> RepairRequestPacket:
    return RepairRequestPacket(
        problem_id=kwargs.get("problem_id", ""),
        stmt=kwargs.get("stmt", ""),
        theory_context=kwargs.get("theory_context", ""),
        retry_instruction=kwargs.get("retry_instruction", "") or "",
        error_fingerprint=kwargs.get("error_fingerprint", "") or "",
        error_categories=_as_str_list(kwargs.get("error_categories", [])),
        previous_result=kwargs.get("previous_result", "") or "",
        previous_proof_sketch=kwargs.get("previous_proof_sketch", "") or "",
        previous_prelude_code=kwargs.get("previous_prelude_code", "") or "",
        previous_proof_text=kwargs.get("previous_proof_text", "") or "",
        previous_counterexample_text=kwargs.get("previous_counterexample_text", "") or "",
        repair_history_tail=_coerce_rows(kwargs.get("repair_history_tail", [])),
        lean_error_excerpt=kwargs.get("lean_error_excerpt", "") or "",
        lean_error_top_lines=_as_str_list(kwargs.get("lean_error_top_lines", [])),
        lean_diagnostics=kwargs.get("lean_diagnostics", "") or "",
        current_scratch_code=kwargs.get("current_scratch_code", "") or "",
        mathlib_import_in_scratch=bool(kwargs.get("mathlib_import_in_scratch", True)),
        new_problem_generation_policy=_coerce_bool_map(
            kwargs.get("new_problem_generation_policy", {})
        )
        or {
            "prefer_subgoals_when_stuck": True,
            "avoid_generalization_when_stuck": True,
            "prefer_intermediate_lemmas": True,
            "avoid_direct_axiom_instantiation": True,
            "avoid_variable_renaming_only": True,
            "target_novelty": "medium_or_high",
        },
    )
