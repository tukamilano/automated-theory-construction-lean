from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

from common import (
    ARCHIVED_PROBLEMS_FILENAME,
    LEGACY_DEFERRED_PROBLEMS_FILENAME,
    LEGACY_PRUNED_OPEN_PROBLEMS_FILENAME,
    write_jsonl_atomic,
)
from run_loop import DERIVED_TEMPLATE, SCRATCH_TEMPLATE, prebuild_lean_project


DEFAULT_THEORY = Path("AutomatedTheoryConstruction/Theory.lean")
DEFAULT_DERIVED = Path("AutomatedTheoryConstruction/Derived.lean")
DEFAULT_OUTPUT = Path("AutomatedTheoryConstruction/seeds.jsonl")
DEFAULT_REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_DATA_DIR = Path("data")
DEFAULT_SCRATCH = Path("AutomatedTheoryConstruction/Scratch.lean")
DEFAULT_FORMALIZATION_MEMORY = Path("data/formalization_memory.json")
DEFAULT_ARCHIVED = Path("data/archived_problems.jsonl")


def _preview_file_for(derived_file: Path) -> Path:
    return derived_file.with_name(f"{derived_file.stem}.refactored.preview{derived_file.suffix}")


def _reviewed_file_for(derived_file: Path) -> Path:
    return derived_file.with_name(f"{derived_file.stem}.refactored.reviewed{derived_file.suffix}")


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

    scratch_file.parent.mkdir(parents=True, exist_ok=True)
    scratch_file.write_text(SCRATCH_TEMPLATE, encoding="utf-8")

    derived_file.parent.mkdir(parents=True, exist_ok=True)
    derived_file.write_text(DERIVED_TEMPLATE, encoding="utf-8")
    for cleanup_file in derived_cleanup_files:
        cleanup_file.unlink(missing_ok=True)

    formalization_memory_file.parent.mkdir(parents=True, exist_ok=True)
    formalization_memory_file.write_text("{}\n", encoding="utf-8")


def sync_open_problems_from_seed_rows(*, data_dir: Path, rows: list[dict[str, Any]]) -> None:
    write_jsonl_atomic(data_dir / "open_problems.jsonl", rows)


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
    theory_file: Path,
    derived_file: Path | None,
    context_files: list[Path],
    seed_count: int,
    extra_instruction: str,
) -> str:
    read_lines = [f"- {theory_file.resolve()}"]
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

    return f"""Read these files before generating seeds:
{chr(10).join(read_lines)}

Task:
- Generate {seed_count} initial open problems for the automated theory-construction loop.
- Base every candidate on the actual definitions, notation, classes, axioms, and proved lemmas visible in the files above.
- Stay faithful to the mathematics already described in those files.
- Generate statements that remain within the concepts and proof-relevant structure that `Theory.lean` can actually express and manipulate.
- Each candidate must be one standalone Lean proposition string suitable for the `stmt` field in `seeds.jsonl`.

Mathematical scope:
- Prefer statements that materially sharpen or extend the visible theory: structural consequences, converses or separations, existence or uniqueness claims, impossibility claims, fixpoint consequences, or useful intermediate lemmas.
- Do not default to immediate one-line corollaries or cosmetic rewrites of visible lemmas.
- Use only objects, notation, classes, predicates, and constructions that already exist in the files above.
- Reuse exact symbol names from the source files. Do not invent new definitions or predicates.
- Quantify every extra variable or witness explicitly inside the proposition.
- Keep assumptions minimal but sufficient.

Quality filter:
- Do not restate declarations already proved in `{theory_file.resolve()}`.
{derived_rule}- Do not propose a theorem that is already present in the read files up to cosmetic rewrites, alpha-renaming, trivial reassociation of binders, or other shallow reformulations.
- Do not propose propositions that are vacuous, purely definitional unfoldings, or trivial preorder facts.
- Avoid seeds that differ only by notation changes, variable renaming, or tiny local rewrites.
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


def run_codex(
    *,
    prompt: str,
    schema: dict[str, Any],
    repo_root: Path,
    sandbox: str,
    model: str | None,
) -> str:
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", delete=False, suffix=".json") as schema_handle:
        json.dump(schema, schema_handle, ensure_ascii=False, indent=2)
        schema_path = Path(schema_handle.name)

    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", delete=False, suffix=".txt") as output_handle:
        output_path = Path(output_handle.name)

    try:
        cmd = [
            "codex",
            "exec",
            "-",
            "--sandbox",
            sandbox,
            "--skip-git-repo-check",
            "--output-schema",
            str(schema_path),
            "--output-last-message",
            str(output_path),
        ]
        if model:
            cmd.extend(["--model", model])

        completed = subprocess.run(
            cmd,
            input=prompt,
            text=True,
            cwd=str(repo_root),
            capture_output=True,
            check=False,
        )
        if completed.returncode != 0:
            stderr = (completed.stderr or "").strip()
            raise RuntimeError(f"codex exec failed ({completed.returncode}): {stderr}")

        text = output_path.read_text(encoding="utf-8") if output_path.exists() else ""
        if not text.strip():
            text = (completed.stdout or "").strip()
        if not text.strip():
            raise RuntimeError("codex exec returned no final message")
        return text
    finally:
        schema_path.unlink(missing_ok=True)
        output_path.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate seeds.jsonl from Theory.lean using `codex exec`."
    )
    parser.add_argument("--theory-file", default=str(DEFAULT_THEORY))
    parser.add_argument("--derived-file", default=str(DEFAULT_DERIVED))
    parser.add_argument("--output-file", default=str(DEFAULT_OUTPUT))
    parser.add_argument("--seed-count", type=int, default=4)
    parser.add_argument("--seed-src", default="seed")
    parser.add_argument("--context-file", action="append", default=[])
    parser.add_argument("--extra-instruction", default="")
    parser.add_argument("--model")
    parser.add_argument("--sandbox", default="read-only")
    parser.add_argument("--repo-root", default=str(DEFAULT_REPO_ROOT))
    parser.add_argument("--initialize-runtime-state", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    if args.seed_count <= 0:
        raise SystemExit("--seed-count must be positive")

    repo_root = Path(args.repo_root).resolve()
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

    if args.initialize_runtime_state and not args.dry_run:
        reset_runtime_before_seed_generation(
            data_dir=(repo_root / DEFAULT_DATA_DIR).resolve(),
            seeds_file=output_file,
            scratch_file=(repo_root / DEFAULT_SCRATCH).resolve(),
            derived_file=derived_file,
            derived_cleanup_files=(
                _preview_file_for(derived_file),
                _reviewed_file_for(derived_file),
            ),
            formalization_memory_file=(repo_root / DEFAULT_FORMALIZATION_MEMORY).resolve(),
            archived_problems_file=(repo_root / DEFAULT_ARCHIVED).resolve(),
        )
        prebuild_lean_project()

    if derived_file.exists():
        effective_derived: Path | None = derived_file
    else:
        effective_derived = None

    prompt = build_prompt(
        theory_file=theory_file,
        derived_file=effective_derived,
        context_files=context_files,
        seed_count=args.seed_count,
        extra_instruction=args.extra_instruction,
    )
    schema = build_output_schema(args.seed_count)

    if args.dry_run:
        cmd = [
            "codex",
            "exec",
            "-",
            "--sandbox",
            args.sandbox,
            "--skip-git-repo-check",
            "--output-schema",
            "<temp-schema.json>",
            "--output-last-message",
            "<temp-output.txt>",
        ]
        if args.model:
            cmd.extend(["--model", args.model])
        sys.stdout.write("Command:\n")
        sys.stdout.write(" ".join(cmd) + "\n\n")
        sys.stdout.write("Prompt:\n")
        sys.stdout.write(prompt)
        return 0

    raw_output = run_codex(
        prompt=prompt,
        schema=schema,
        repo_root=repo_root,
        sandbox=args.sandbox,
        model=args.model,
    )
    payload = _extract_json_object(raw_output)
    seeds = validate_seed_payload(payload, args.seed_count)

    rows = [
        {
            "id": f"op_{index:06d}",
            "stmt": stmt,
            "src": args.seed_src,
            "priority": "unknown",
            "priority_rationale": "",
            "failure_count": 0,
        }
        for index, stmt in enumerate(seeds, 1)
    ]
    write_jsonl_atomic(output_file, rows)
    if args.initialize_runtime_state:
        sync_open_problems_from_seed_rows(
            data_dir=(repo_root / DEFAULT_DATA_DIR).resolve(),
            rows=rows,
        )
    sys.stdout.write(f"Wrote {len(rows)} seeds to {output_file}\n")
    if args.initialize_runtime_state:
        sys.stdout.write("Reset runtime state before seed generation and loaded the regenerated seeds into open problems.\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
