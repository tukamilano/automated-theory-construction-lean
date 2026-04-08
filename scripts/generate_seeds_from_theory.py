from __future__ import annotations

import argparse
import json
import sys
import tempfile
from pathlib import Path
from typing import Any

from common import (
    ARCHIVED_PROBLEMS_FILENAME,
    LEGACY_DEFERRED_PROBLEMS_FILENAME,
    LEGACY_PRUNED_OPEN_PROBLEMS_FILENAME,
    dedupe_problem_rows_by_stmt,
    load_theory_context,
    read_jsonl,
    write_jsonl_atomic,
)
from llm_exec import build_exec_command
from llm_exec import resolve_provider
from llm_exec import run_llm_exec
from research_agenda import DEFAULT_RESEARCH_AGENDA_PATH
from research_agenda import format_research_agenda_prompt_block
from research_agenda import load_research_agenda
from run_loop import (
    DERIVED_TEMPLATE,
    SCRATCH_TEMPLATE,
    cleanup_parallel_scratch_files,
    load_theory_state,
    prebuild_lean_project,
    theory_state_path,
)


DEFAULT_THEORY = Path("AutomatedTheoryConstruction/Theory.lean")
DEFAULT_DERIVED = Path("AutomatedTheoryConstruction/Derived.lean")
DEFAULT_OUTPUT = Path("AutomatedTheoryConstruction/seeds.jsonl")
DEFAULT_REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_DATA_DIR = Path("data")
DEFAULT_SCRATCH = Path("AutomatedTheoryConstruction/Scratch.lean")
DEFAULT_FORMALIZATION_MEMORY = Path("data/formalization_memory.json")
DEFAULT_ARCHIVED = Path("data/archived_problems.jsonl")
DEFAULT_RESEARCH_AGENDA = DEFAULT_REPO_ROOT / DEFAULT_RESEARCH_AGENDA_PATH


def _preview_file_for(derived_file: Path) -> Path:
    return derived_file.with_name(f"{derived_file.stem}.refactored.preview{derived_file.suffix}")


def _reviewed_file_for(derived_file: Path) -> Path:
    return derived_file.with_name(f"{derived_file.stem}.refactored.reviewed{derived_file.suffix}")


def _compression_plan_file_for(derived_file: Path) -> Path:
    return derived_file.with_name(f"{derived_file.stem}.compression.plan.json")


def _compression_report_file_for(derived_file: Path) -> Path:
    return derived_file.with_name(f"{derived_file.stem}.compression.report.json")


def _proof_retarget_plan_file_for(derived_file: Path) -> Path:
    return derived_file.with_name(f"{derived_file.stem}.proof_retarget.plan.json")


def _proof_retarget_report_file_for(derived_file: Path) -> Path:
    return derived_file.with_name(f"{derived_file.stem}.proof_retarget.report.json")


def _presentation_plan_file_for(derived_file: Path) -> Path:
    return derived_file.with_name(f"{derived_file.stem}.presentation.plan.json")


def _presentation_report_file_for(derived_file: Path) -> Path:
    return derived_file.with_name(f"{derived_file.stem}.presentation.report.json")


def _refactor_pass_1_log_file_for(derived_file: Path) -> Path:
    return derived_file.with_name(f"{derived_file.stem}.refactor.pass1.log.jsonl")


def _compression_executor_log_file_for(derived_file: Path) -> Path:
    return derived_file.with_name(f"{derived_file.stem}.compression.executor.log.jsonl")


def _proof_retarget_executor_log_file_for(derived_file: Path) -> Path:
    return derived_file.with_name(f"{derived_file.stem}.proof_retarget.executor.log.jsonl")


def _presentation_executor_log_file_for(derived_file: Path) -> Path:
    return derived_file.with_name(f"{derived_file.stem}.presentation.executor.log.jsonl")


def _try_at_each_step_raw_output_file_for(derived_file: Path) -> Path:
    return derived_file.with_name(f"{derived_file.stem}.tryAtEachStep.json")


def _try_at_each_step_apply_report_file_for(derived_file: Path) -> Path:
    return derived_file.with_name(f"{derived_file.stem}.tryAtEachStep.apply_report.json")


def reset_runtime_before_seed_generation(
    *,
    data_dir: Path,
    seeds_file: Path,
    scratch_file: Path,
    derived_file: Path,
    derived_cleanup_files: tuple[Path, ...],
    formalization_memory_file: Path,
    archived_problems_file: Path,
) -> None:
    data_dir.mkdir(parents=True, exist_ok=True)
    seeds_file.unlink(missing_ok=True)
    write_jsonl_atomic(data_dir / "open_problems.jsonl", [])
    write_jsonl_atomic(archived_problems_file, [])
    write_jsonl_atomic(data_dir / "solved_problems.jsonl", [])
    write_jsonl_atomic(data_dir / "counterexamples.jsonl", [])
    (data_dir / LEGACY_DEFERRED_PROBLEMS_FILENAME).unlink(missing_ok=True)
    (data_dir / LEGACY_PRUNED_OPEN_PROBLEMS_FILENAME).unlink(missing_ok=True)
    theory_state_path(data_dir).unlink(missing_ok=True)
    cleanup_parallel_scratch_files(scratch_file)

    scratch_file.parent.mkdir(parents=True, exist_ok=True)
    scratch_file.write_text(SCRATCH_TEMPLATE, encoding="utf-8")

    derived_file.parent.mkdir(parents=True, exist_ok=True)
    derived_file.write_text(DERIVED_TEMPLATE, encoding="utf-8")
    for cleanup_file in derived_cleanup_files:
        cleanup_file.unlink(missing_ok=True)

    formalization_memory_file.parent.mkdir(parents=True, exist_ok=True)
    formalization_memory_file.write_text("{}\n", encoding="utf-8")


def sync_open_problems_from_seed_rows(*, data_dir: Path, rows: list[dict[str, Any]]) -> None:
    write_jsonl_atomic(data_dir / "open_problems.jsonl", dedupe_problem_rows_by_stmt(rows))


def _normalize_stmt(stmt: str) -> str:
    return " ".join(stmt.split())


def _iter_braced_json_candidates(text: str) -> list[str]:
    candidates: list[str] = []
    start_idx: int | None = None
    depth = 0
    in_string = False
    escape = False

    for idx, ch in enumerate(text):
        if in_string:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_string = False
            continue

        if ch == '"':
            in_string = True
            continue

        if ch == "{":
            if depth == 0:
                start_idx = idx
            depth += 1
            continue

        if ch == "}" and depth > 0:
            depth -= 1
            if depth == 0 and start_idx is not None:
                candidates.append(text[start_idx : idx + 1])
                start_idx = None

    return candidates


def _extract_json_object(text: str) -> dict[str, Any]:
    raw = text.strip()
    if not raw:
        raise ValueError("empty model output")

    try:
        payload = json.loads(raw)
        if isinstance(payload, dict):
            return payload
    except json.JSONDecodeError:
        pass

    for candidate in _iter_braced_json_candidates(raw):
        try:
            payload = json.loads(candidate)
        except json.JSONDecodeError:
            continue
        if isinstance(payload, dict):
            return payload

    raise ValueError("model output did not contain a parseable JSON object")


def build_prompt(
    *,
    theory_files: list[Path],
    derived_file: Path | None,
    context_files: list[Path],
    seed_count: int,
    extra_instruction: str,
    theory_state: dict[str, Any] | None = None,
    research_agenda: dict[str, Any] | None = None,
    recent_opportunities: list[dict[str, Any]] | None = None,
) -> str:
    if not theory_files:
        raise ValueError("theory_files must be non-empty")

    read_lines = [f"- {path.resolve()}" for path in theory_files]
    if derived_file is not None:
        read_lines.append(f"- {derived_file.resolve()}")
    for path in context_files:
        read_lines.append(f"- {path.resolve()}")

    derived_rule = (
        f"- Do not restate theorems already proved in `{derived_file.resolve()}`.\n"
        if derived_file is not None
        else ""
    )
    extra_block = f"- Additional guidance: {extra_instruction.strip()}\n" if extra_instruction.strip() else ""
    theory_files_rule = "- Do not restate declarations already present in the theory files listed above.\n"
    theory_summary_block = ""
    counterexample_block = ""
    next_direction_block = ""
    theory_frontier_block = ""
    opportunity_block = ""
    research_agenda_block = format_research_agenda_prompt_block(research_agenda)
    state = dict(theory_state or {})
    theory_snapshot = str(state.get("theory_snapshot", "")).strip()
    direction = state.get("next_direction")
    important_counterexamples = state.get("important_verified_counterexamples", [])
    desired_summary_changes = state.get("desired_summary_changes", [])
    current_bottlenecks = state.get("current_bottlenecks", [])
    overexplored_patterns = state.get("overexplored_patterns", [])
    missing_bridges = state.get("missing_bridges", [])
    agenda_pressure = state.get("agenda_pressure", [])
    if theory_snapshot:
        theory_summary_block += f"- Current theory snapshot: {theory_snapshot}\n"
    if isinstance(important_counterexamples, list):
        normalized_counterexamples = [str(item).strip() for item in important_counterexamples if str(item).strip()]
        if normalized_counterexamples:
            counterexample_block += (
                "- Important verified counterexamples to respect: "
                f"{'; '.join(normalized_counterexamples[:3])}\n"
            )
            counterexample_block += (
                "- Use these counterexamples as boundary evidence: avoid proposing false overgeneralizations, and prefer sharpened hypotheses, exact regimes, or separation statements when they look stronger.\n"
            )
    if isinstance(direction, dict):
        guidance = str(direction.get("guidance", "")).strip()
        rationale = str(direction.get("rationale", "")).strip()
        if guidance:
            next_direction_block += (
                "- Strongly prefer seed problems that follow the current next direction: "
                f"{guidance}\n"
            )
        if rationale:
            next_direction_block += f"- Why this direction matters now: {rationale}\n"
        if guidance:
            next_direction_block += (
                "- This direction is a strong preference, not a hard constraint. Keep some diversity and allow a small number of clearly stronger problems outside it.\n"
            )
    if isinstance(desired_summary_changes, list):
        normalized_summary_changes = [str(item).strip() for item in desired_summary_changes if str(item).strip()]
        if normalized_summary_changes:
            theory_frontier_block += (
                "- Prefer problems whose resolution would change the theory summary in one of these ways: "
                f"{'; '.join(normalized_summary_changes[:4])}\n"
            )
    if isinstance(current_bottlenecks, list):
        normalized_bottlenecks = [str(item).strip() for item in current_bottlenecks if str(item).strip()]
        if normalized_bottlenecks:
            theory_frontier_block += (
                "- Current bottlenecks to address: "
                f"{'; '.join(normalized_bottlenecks[:4])}\n"
            )
    if isinstance(missing_bridges, list):
        normalized_missing_bridges = [str(item).strip() for item in missing_bridges if str(item).strip()]
        if normalized_missing_bridges:
            theory_frontier_block += (
                "- Missing bridges worth targeting: "
                f"{'; '.join(normalized_missing_bridges[:4])}\n"
            )
    if isinstance(overexplored_patterns, list):
        normalized_overexplored_patterns = [str(item).strip() for item in overexplored_patterns if str(item).strip()]
        if normalized_overexplored_patterns:
            theory_frontier_block += (
                "- Strongly down-rank problems that fit these overexplored patterns unless they unlock a broader structural step: "
                f"{'; '.join(normalized_overexplored_patterns[:4])}\n"
            )
    if isinstance(agenda_pressure, list):
        normalized_agenda_pressure = [str(item).strip() for item in agenda_pressure if str(item).strip()]
        if normalized_agenda_pressure:
            theory_frontier_block += (
                "- Additional progress pressure from the current theory state: "
                f"{'; '.join(normalized_agenda_pressure[:4])}\n"
            )
    if isinstance(recent_opportunities, list):
        rendered_opportunities: list[str] = []
        for item in recent_opportunities:
            if not isinstance(item, dict):
                continue
            opportunity = item.get("opportunity")
            if not isinstance(opportunity, dict):
                continue
            statement = str(opportunity.get("statement", "")).strip()
            kind = str(opportunity.get("kind", "")).strip()
            unlocks = str(opportunity.get("unlocks", "")).strip()
            if not statement or not kind or not unlocks:
                continue
            rendered_opportunities.append(f"{kind}: {statement} [unlocks: {unlocks}]")
        if rendered_opportunities:
            opportunity_block += (
                "- Recent post-solve opportunities (signal only, not mandatory targets): "
                f"{'; '.join(rendered_opportunities[:3])}\n"
            )

    return f"""Read these files before generating seeds:
{chr(10).join(read_lines)}

Task:
- Generate {seed_count} initial open problems for the automated theory-construction loop.
- Base every candidate on the actual definitions, notation, classes, axioms, and proved lemmas visible in the files above.
- Stay faithful to the mathematics already described in those files.
- Treat the first listed Lean file as the theory entry point and include any locally imported theory submodules in scope.
- Generate statements that remain within the concepts and proof-relevant structure that the theory entry and its imported local modules can actually express and manipulate.
- Each candidate must be one standalone Lean proposition string suitable for the `stmt` field in `seeds.jsonl`.

Mathematical scope:
- Treat `theory_state` and `research_agenda` as primary guidance for what counts as meaningful progress.
- Prefer statements that materially sharpen or extend the visible theory: structural consequences, converses or separations, existence or uniqueness claims, impossibility claims, fixpoint consequences, or useful intermediate lemmas.
- Prefer problems that would change the theory summary, address a bottleneck, or connect currently separate parts of the theory.
- Do not default to immediate one-line corollaries or cosmetic rewrites of visible lemmas.
- Use only objects, notation, classes, predicates, and constructions that already exist in the files above.
- Reuse exact symbol names from the source files. Do not invent new definitions or predicates.
- Quantify every extra variable or witness explicitly inside the proposition.
- Keep assumptions minimal but sufficient.
{theory_summary_block}{counterexample_block}{next_direction_block}{theory_frontier_block}{opportunity_block}{research_agenda_block}

Quality filter:
{theory_files_rule}{derived_rule}- Do not propose a theorem that is already present in the read files up to cosmetic rewrites, alpha-renaming, trivial reassociation of binders, or other shallow reformulations.
- Do not propose propositions that are vacuous, purely definitional unfoldings, or trivial preorder facts.
- Avoid seeds that differ only by notation changes, variable renaming, or tiny local rewrites.
- Strongly avoid safe peripheral extensions that fit known overexplored patterns unless they are the clearest route to a broader organizing result.
- Keep the seeds mathematically diverse when possible.
- Make each proposition read like something that could be pasted directly into a theorem statement in Lean.
{extra_block}
Output contract:
- Return exactly one JSON object and nothing else.
- The JSON object must have exactly this shape: {{"seeds": ["stmt1", "stmt2"]}}
- Return exactly {seed_count} seed statements.
- Do not include markdown fences.
- Do not include ids, rationale, commentary, theorem names, or surrounding prose.
"""


def build_output_schema(seed_count: int) -> dict[str, Any]:
    return {
        "type": "object",
        "properties": {
            "seeds": {
                "type": "array",
                "minItems": seed_count,
                "maxItems": seed_count,
                "items": {
                    "type": "string",
                    "minLength": 1,
                },
            }
        },
        "required": ["seeds"],
        "additionalProperties": False,
    }


def validate_seed_payload(payload: dict[str, Any], seed_count: int) -> list[str]:
    seeds_value = payload.get("seeds")
    if not isinstance(seeds_value, list):
        raise ValueError("`seeds` must be an array")
    if len(seeds_value) != seed_count:
        raise ValueError(f"expected {seed_count} seeds, got {len(seeds_value)}")

    seeds: list[str] = []
    seen_norms: set[str] = set()
    for idx, item in enumerate(seeds_value, 1):
        if not isinstance(item, str):
            raise ValueError(f"seed {idx} is not a string")
        stmt = item.strip()
        if not stmt:
            raise ValueError(f"seed {idx} is empty")
        norm = _normalize_stmt(stmt)
        if norm in seen_norms:
            raise ValueError(f"duplicate seed statement at index {idx}")
        seen_norms.add(norm)
        seeds.append(stmt)
    return seeds


def build_batch_generator_rows(*, seeds: list[str], seed_src: str) -> list[dict[str, Any]]:
    return [
        {
            "id": f"op_{index:06d}",
            "stmt": stmt,
            "src": seed_src,
            "priority": "unknown",
            "priority_rationale": "",
            "failure_count": 0,
        }
        for index, stmt in enumerate(seeds, 1)
    ]


def run_llm(
    *,
    prompt: str,
    schema: dict[str, Any],
    repo_root: Path,
    sandbox: str,
    provider: str,
    model: str | None,
) -> str:
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", delete=False, suffix=".json") as schema_handle:
        json.dump(schema, schema_handle, ensure_ascii=False, indent=2)
        schema_path = Path(schema_handle.name)

    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", delete=False, suffix=".txt") as output_handle:
        output_path = Path(output_handle.name)

    try:
        completed = run_llm_exec(
            provider=provider,
            prompt=prompt,
            sandbox=sandbox,
            model=model,
            cwd=repo_root,
            output_schema_path=schema_path,
            output_last_message_path=output_path,
        )
        if completed.returncode != 0:
            stderr = (completed.stderr or "").strip()
            raise RuntimeError(f"{provider} exec failed ({completed.returncode}): {stderr}")

        text = output_path.read_text(encoding="utf-8") if output_path.exists() else ""
        if not text.strip():
            text = (completed.stdout or "").strip()
        if not text.strip():
            raise RuntimeError(f"{provider} exec returned no final message")
        return text
    finally:
        schema_path.unlink(missing_ok=True)
        output_path.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate a batch of open-problem candidates from a Theory.lean entry module using the configured LLM CLI."
    )
    parser.add_argument("--theory-file", default=str(DEFAULT_THEORY))
    parser.add_argument("--derived-file", default=str(DEFAULT_DERIVED))
    parser.add_argument("--output-file", default=str(DEFAULT_OUTPUT))
    parser.add_argument("--seed-count", type=int, default=4)
    parser.add_argument("--seed-src", default="seed")
    parser.add_argument("--context-file", action="append", default=[])
    parser.add_argument("--extra-instruction", default="")
    parser.add_argument("--provider")
    parser.add_argument("--model")
    parser.add_argument("--sandbox", default="read-only")
    parser.add_argument("--repo-root", default=str(DEFAULT_REPO_ROOT))
    parser.add_argument("--initialize-runtime-state", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    if args.seed_count <= 0:
        raise SystemExit("--seed-count must be positive")

    repo_root = Path(args.repo_root).resolve()
    provider = resolve_provider(args.provider)
    theory_file = (repo_root / args.theory_file).resolve() if not Path(args.theory_file).is_absolute() else Path(args.theory_file)
    derived_arg = Path(args.derived_file)
    derived_file = (repo_root / derived_arg).resolve() if not derived_arg.is_absolute() else derived_arg.resolve()
    output_file = (repo_root / args.output_file).resolve() if not Path(args.output_file).is_absolute() else Path(args.output_file)
    context_files = [
        (repo_root / Path(raw)).resolve() if not Path(raw).is_absolute() else Path(raw).resolve()
        for raw in args.context_file
    ]

    if not theory_file.exists():
        raise SystemExit(f"Theory file not found: {theory_file}")
    for path in context_files:
        if not path.exists():
            raise SystemExit(f"Context file not found: {path}")

    theory_files, _ = load_theory_context(theory_file, repo_root=repo_root)
    if not theory_files:
        raise SystemExit(f"Failed to resolve theory context files from: {theory_file}")

    if args.initialize_runtime_state and not args.dry_run:
        reset_runtime_before_seed_generation(
            data_dir=(repo_root / DEFAULT_DATA_DIR).resolve(),
            seeds_file=output_file,
            scratch_file=(repo_root / DEFAULT_SCRATCH).resolve(),
            derived_file=derived_file,
            derived_cleanup_files=(
                _preview_file_for(derived_file),
                _compression_plan_file_for(derived_file),
                _compression_report_file_for(derived_file),
                _proof_retarget_plan_file_for(derived_file),
                _proof_retarget_report_file_for(derived_file),
                _presentation_plan_file_for(derived_file),
                _presentation_report_file_for(derived_file),
                _refactor_pass_1_log_file_for(derived_file),
                _compression_executor_log_file_for(derived_file),
                _proof_retarget_executor_log_file_for(derived_file),
                _presentation_executor_log_file_for(derived_file),
                _reviewed_file_for(derived_file),
                _try_at_each_step_raw_output_file_for(derived_file),
                _try_at_each_step_apply_report_file_for(derived_file),
            ),
            formalization_memory_file=(repo_root / DEFAULT_FORMALIZATION_MEMORY).resolve(),
            archived_problems_file=(repo_root / DEFAULT_ARCHIVED).resolve(),
        )
        prebuild_lean_project()

    if derived_file.exists():
        effective_derived: Path | None = derived_file
    else:
        effective_derived = None
    effective_theory_state = load_theory_state((repo_root / DEFAULT_DATA_DIR).resolve())
    effective_research_agenda = load_research_agenda(DEFAULT_RESEARCH_AGENDA)
    recent_opportunities = read_jsonl((repo_root / DEFAULT_DATA_DIR / "post_solve_opportunities.jsonl").resolve())[-12:]

    prompt = build_prompt(
        theory_files=theory_files,
        derived_file=effective_derived,
        context_files=context_files,
        seed_count=args.seed_count,
        extra_instruction=args.extra_instruction,
        theory_state=effective_theory_state,
        research_agenda=effective_research_agenda,
        recent_opportunities=recent_opportunities,
    )
    schema = build_output_schema(args.seed_count)

    if args.dry_run:
        cmd = build_exec_command(
            provider=provider,
            sandbox=args.sandbox,
            model=args.model,
            output_schema_path=Path("<temp-schema.json>"),
            output_last_message_path=Path("<temp-output.txt>"),
        )
        sys.stdout.write("Command:\n")
        sys.stdout.write(" ".join(cmd) + "\n\n")
        sys.stdout.write("Prompt:\n")
        sys.stdout.write(prompt)
        return 0

    raw_output = run_llm(
        prompt=prompt,
        schema=schema,
        repo_root=repo_root,
        sandbox=args.sandbox,
        provider=provider,
        model=args.model,
    )
    payload = _extract_json_object(raw_output)
    seeds = validate_seed_payload(payload, args.seed_count)

    rows = build_batch_generator_rows(
        seeds=seeds,
        seed_src=args.seed_src,
    )
    write_jsonl_atomic(output_file, rows)
    if args.initialize_runtime_state:
        sync_open_problems_from_seed_rows(
            data_dir=(repo_root / DEFAULT_DATA_DIR).resolve(),
            rows=rows,
        )
    sys.stdout.write(f"Wrote {len(rows)} batch-generated problems to {output_file}\n")
    if args.initialize_runtime_state:
        sys.stdout.write("Reset runtime state before seed generation and loaded the regenerated seeds into open problems.\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
