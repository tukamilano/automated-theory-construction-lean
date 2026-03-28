from __future__ import annotations

import argparse
import shutil
import sys
import tempfile
from pathlib import Path

from llm_exec import build_exec_command
from llm_exec import resolve_provider
from llm_exec import run_llm_exec


DEFAULT_INPUT = Path("AutomatedTheoryConstruction/Derived.refactored.preview.lean")
DEFAULT_OUTPUT = Path("AutomatedTheoryConstruction/Derived.refactored.reviewed.lean")
DEFAULT_POLICY = Path(".agents/shared/skills/lean-review-refactor-policy/SKILL.md")
DEFAULT_LEAN_RULE = Path(".agents/shared/skills/lean-rule/SKILL.md")
DEFAULT_MATHLIB_USAGE = Path(".agents/shared/skills/mathlib-usage/SKILL.md")


def build_prompt(
    *,
    input_file: Path,
    output_file: Path,
    verify: bool,
    policy_file: Path,
    lean_rule_file: Path,
    mathlib_usage_file: Path,
) -> str:
    verify_step = (
        f"- Run `lake env lean {output_file}` after each meaningful edit and fix any resulting errors.\n"
        if verify
        else ""
    )
    final_step = (
        f"- Before finishing, run `lake env lean {output_file}` and ensure it succeeds.\n"
        if verify
        else ""
    )
    return f"""Use these repository-local guidance files while you work:
- {policy_file}
- {lean_rule_file}
- {mathlib_usage_file}

Task:
- Review-polish `{output_file}` as a non-semantic refactor.
- `{output_file}` was copied from `{input_file}` and should be edited in place.
- Preserve all public theorem names, theorem statements, namespace structure, and intended API.
- Do not redesign the theorem inventory.
- Prefer review-focused cleanup only: localize `classical`, remove brittle proof steps, tidy `have` structure, remove `by exact`, and prefer stable rewrites / `simpa` / short `calc` blocks.
- For main-theorem-style results, prefer rewriting proofs to explicitly reuse existing `Derived.lean` theorems when that can be done without changing statements.
- Do not introduce `sorry`.
- Do not add or remove global instances, `[simp]` attributes, notation, coercions, or transparency changes.
{verify_step}{final_step}
When finished, give a short summary of the non-semantic cleanup you made and whether the final Lean check passed.
"""


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Thin wrapper around the configured LLM CLI for review-polishing Derived Lean files."
    )
    parser.add_argument("--input-file", default=str(DEFAULT_INPUT))
    parser.add_argument("--output-file", default=str(DEFAULT_OUTPUT))
    parser.add_argument("--provider")
    parser.add_argument("--model")
    parser.add_argument("--sandbox", default="workspace-write")
    parser.add_argument("--skip-copy", action="store_true")
    parser.add_argument("--no-verify", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--policy-file", default=str(DEFAULT_POLICY))
    parser.add_argument("--lean-rule-file", default=str(DEFAULT_LEAN_RULE))
    parser.add_argument("--mathlib-usage-file", default=str(DEFAULT_MATHLIB_USAGE))
    args = parser.parse_args()

    input_file = Path(args.input_file)
    output_file = Path(args.output_file)
    provider = resolve_provider(args.provider)
    policy_file = Path(args.policy_file)
    lean_rule_file = Path(args.lean_rule_file)
    mathlib_usage_file = Path(args.mathlib_usage_file)

    if not input_file.exists():
        raise SystemExit(f"Input file not found: {input_file}")
    for path in (policy_file, lean_rule_file, mathlib_usage_file):
        if not path.exists():
            raise SystemExit(f"Guidance file not found: {path}")

    output_file.parent.mkdir(parents=True, exist_ok=True)
    if not args.skip_copy:
        shutil.copyfile(input_file, output_file)

    prompt = build_prompt(
        input_file=input_file,
        output_file=output_file,
        verify=not args.no_verify,
        policy_file=policy_file,
        lean_rule_file=lean_rule_file,
        mathlib_usage_file=mathlib_usage_file,
    )

    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", delete=False, suffix=".txt") as handle:
        handle.write(prompt)
        prompt_path = Path(handle.name)

    cmd = build_exec_command(
        provider=provider,
        sandbox=args.sandbox,
        model=args.model,
    )

    if args.dry_run:
        sys.stdout.write("Command:\n")
        sys.stdout.write(" ".join(cmd) + "\n\n")
        sys.stdout.write(f"Prompt file: {prompt_path}\n")
        return 0

    try:
        completed = run_llm_exec(
            provider=provider,
            prompt=prompt,
            sandbox=args.sandbox,
            model=args.model,
            capture_output=False,
        )
        return completed.returncode
    finally:
        prompt_path.unlink(missing_ok=True)


if __name__ == "__main__":
    raise SystemExit(main())
