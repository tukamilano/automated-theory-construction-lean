from __future__ import annotations

import argparse
import json
import re
import subprocess
import tempfile
from pathlib import Path
from typing import Any

from import_inference import infer_minimal_imports, render_import_block


DECL_NAME_PATTERN = re.compile(r"^\s*(lemma|theorem)\s+([A-Za-z0-9_']+)\b")
NAMESPACE_PATTERN = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.']+)\s*$")
END_NAMESPACE_PATTERN = re.compile(r"^\s*end\s+([A-Za-z0-9_.']+)\s*$")


def build_statement_entries_from_file(
    lean_file: Path,
    *,
    max_decls: int | None = None,
) -> list[dict[str, str]]:
    if not lean_file.exists():
        return []
    try:
        content = lean_file.read_text(encoding="utf-8")
    except Exception:
        return []

    entries: list[dict[str, str]] = []
    namespace_stack: list[str] = []
    for line in content.splitlines():
        namespace_match = NAMESPACE_PATTERN.match(line)
        if namespace_match:
            namespace_name = namespace_match.group(1).strip()
            namespace_stack.append(namespace_name)
            continue

        end_namespace_match = END_NAMESPACE_PATTERN.match(line)
        if end_namespace_match:
            namespace_name = end_namespace_match.group(1).strip()
            if namespace_stack and namespace_stack[-1] == namespace_name:
                namespace_stack.pop()
            continue

        match = DECL_NAME_PATTERN.match(line)
        if not match:
            continue
        decl_kind = match.group(1).strip()
        decl_name = match.group(2).strip()
        if not decl_name:
            continue
        full_name = ".".join([*namespace_stack, decl_name]) if namespace_stack else decl_name
        entries.append(
            {
                "kind": decl_kind,
                "label": f"{lean_file.name}::{full_name}",
                "lean_name": full_name,
            }
        )
        if max_decls is not None and len(entries) >= max_decls:
            break
    return entries


def _lean_string_literal(text: str) -> str:
    return json.dumps(text, ensure_ascii=False)


def _render_name_array(names: list[str]) -> str:
    if not names:
        return "#[]"
    return "#[" + ", ".join(f"`{name}" for name in names) + "]"


def _render_label_array(labels: list[str]) -> str:
    if not labels:
        return "#[]"
    return "#[" + ", ".join(_lean_string_literal(label) for label in labels) + "]"


def build_alpha_filter_lean_source(
    *,
    candidate_statement: str,
    entries: list[dict[str, str]],
) -> str:
    existing_names: list[str] = []
    existing_labels: list[str] = []
    for entry in entries:
        existing_names.append(str(entry["lean_name"]))
        existing_labels.append(str(entry["label"]))

    extra_imports = render_import_block(infer_minimal_imports(candidate_statement))
    return f"""{extra_imports}import Lean
import Lean.Data.Json
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

open Lean

namespace AutomatedTheoryConstructionStatementAlphaFilter

axiom candidateStmt : {candidate_statement}

def existingNames : Array Name := {_render_name_array(existing_names)}
def existingLabels : Array String := {_render_label_array(existing_labels)}

def emitPayload (candidateElaborated : Bool) (isDuplicate : Bool) (matchedNames : Array String) (error : String) : CoreM Unit := do
  let payload :=
    Json.mkObj [
      ("candidate_elaborated", toJson candidateElaborated),
      ("is_duplicate", toJson isDuplicate),
      ("matched_names", toJson matchedNames),
      ("error", toJson error)
    ]
  let _ ← IO.println (Json.compress payload)
  return ()

#eval show CoreM Unit from do
  let env ← getEnv
  let candidateName : Name := `AutomatedTheoryConstructionStatementAlphaFilter.candidateStmt
  let some candidateInfo := env.find? candidateName
    | emitPayload true false #[] "candidate declaration missing"
      return ()
  let candidateType := candidateInfo.type.cleanupAnnotations
  let mut hits : Array String := #[]
  for h : i in [:existingNames.size] do
    let some existingInfo := env.find? existingNames[i]
      | continue
    let existingType := existingInfo.type.cleanupAnnotations
    if candidateType.eqv existingType then
      hits := hits.push existingLabels[i]
  emitPayload true (not hits.isEmpty) hits ""

end AutomatedTheoryConstructionStatementAlphaFilter
"""


def build_statement_elaboration_check_source(
    *,
    candidate_statement: str,
) -> str:
    extra_imports = render_import_block(infer_minimal_imports(candidate_statement))
    return f"""{extra_imports}import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstructionStatementAlphaFilter

axiom candidateStmt : {candidate_statement}

end AutomatedTheoryConstructionStatementAlphaFilter
"""


def _run_lean_source(
    *,
    theory_file: Path,
    prefix: str,
    lean_source: str,
    timeout_sec: int,
) -> tuple[bool, str]:
    with tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        suffix=".lean",
        prefix=prefix,
        dir=str(theory_file.parent),
        delete=False,
    ) as handle:
        temp_path = Path(handle.name)
        handle.write(lean_source)

    try:
        try:
            proc = subprocess.run(
                ["lake", "env", "lean", str(temp_path)],
                capture_output=True,
                text=True,
                timeout=timeout_sec,
                check=False,
            )
        except subprocess.TimeoutExpired as exc:
            stderr_text = (exc.stderr or "") if isinstance(exc.stderr, str) else ""
            return False, f"timed out after {timeout_sec}s: {stderr_text}".strip()

        if proc.returncode != 0:
            stderr = (proc.stderr or "").strip()
            stdout = (proc.stdout or "").strip()
            excerpt = (stderr or stdout).splitlines()[0] if (stderr or stdout) else "Lean check failed"
            return False, excerpt

        return True, (proc.stdout or "").strip()
    finally:
        temp_path.unlink(missing_ok=True)


def run_statement_alpha_filter(
    *,
    candidate_statement: str,
    theory_file: Path,
    derived_file: Path,
    timeout_sec: int = 60,
) -> dict[str, Any]:
    elaboration_source = build_statement_elaboration_check_source(
        candidate_statement=candidate_statement,
    )
    elaborated, elaboration_detail = _run_lean_source(
        theory_file=theory_file,
        prefix="StatementElabCheck.",
        lean_source=elaboration_source,
        timeout_sec=max(10, timeout_sec),
    )
    if not elaborated:
        prefix = "statement elaboration timed out" if "timed out" in elaboration_detail else "statement elaboration failed"
        return {
            "candidate_elaborated": False,
            "is_duplicate": False,
            "matched_names": [],
            "duplicate_check_timed_out": False,
            "error": f"{prefix}: {elaboration_detail}".strip(),
        }

    entries = build_statement_entries_from_file(theory_file) + build_statement_entries_from_file(derived_file)
    lean_source = build_alpha_filter_lean_source(
        candidate_statement=candidate_statement,
        entries=entries,
    )
    ok, output = _run_lean_source(
        theory_file=theory_file,
        prefix="StatementAlphaFilter.",
        lean_source=lean_source,
        timeout_sec=timeout_sec,
    )
    if not ok:
        if "timed out" in output:
            return {
                "candidate_elaborated": True,
                "is_duplicate": False,
                "matched_names": [],
                "duplicate_check_timed_out": True,
                "error": f"alpha filter {output}".strip(),
            }
        parsed: dict[str, Any] | None = None
        for line in reversed(output.splitlines()):
            text = line.strip()
            if not text:
                continue
            try:
                payload = json.loads(text)
            except json.JSONDecodeError:
                continue
            if isinstance(payload, dict):
                parsed = payload
                break

        return {
            "candidate_elaborated": False,
            "is_duplicate": False,
            "matched_names": [],
            "duplicate_check_timed_out": False,
            "error": f"alpha filter failed: {output}".strip(),
        }

    parsed: dict[str, Any] | None = None
    for line in reversed(output.splitlines()):
        text = line.strip()
        if not text:
            continue
        try:
            payload = json.loads(text)
        except json.JSONDecodeError:
            continue
        if isinstance(payload, dict):
            parsed = payload
            break

    if parsed is None:
        return {
            "candidate_elaborated": True,
            "is_duplicate": False,
            "matched_names": [],
            "duplicate_check_timed_out": False,
            "error": "alpha filter did not emit a JSON payload",
        }

    matched_names = parsed.get("matched_names", [])
    if not isinstance(matched_names, list):
        matched_names = []

    return {
        "candidate_elaborated": bool(parsed.get("candidate_elaborated", False)),
        "is_duplicate": bool(parsed.get("is_duplicate", False)),
        "matched_names": [str(item) for item in matched_names if str(item).strip()],
        "duplicate_check_timed_out": False,
        "error": str(parsed.get("error", "")).strip(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Filter candidate statements against Theory/Derived using Lean alpha-equivalence.")
    parser.add_argument("--candidate-statement")
    parser.add_argument("--candidate-file")
    parser.add_argument("--theory-file", default="AutomatedTheoryConstruction/Theory.lean")
    parser.add_argument("--derived-file", default="AutomatedTheoryConstruction/Derived.lean")
    parser.add_argument("--timeout", type=int, default=60)
    args = parser.parse_args()

    if bool(args.candidate_statement) == bool(args.candidate_file):
        raise ValueError("Use exactly one of --candidate-statement or --candidate-file")

    if args.candidate_statement is not None:
        candidate_statement = args.candidate_statement
    else:
        candidate_statement = Path(args.candidate_file).read_text(encoding="utf-8")

    result = run_statement_alpha_filter(
        candidate_statement=candidate_statement,
        theory_file=Path(args.theory_file),
        derived_file=Path(args.derived_file),
        timeout_sec=args.timeout,
    )
    print(json.dumps(result, ensure_ascii=False))


if __name__ == "__main__":
    main()
