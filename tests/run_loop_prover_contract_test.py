from __future__ import annotations

import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))


import run_loop


def main() -> int:
    legacy_packet = run_loop.validate_prover_output(
        {
            "problem_id": "op_000001",
            "result": "stuck",
            "proof_sketch": "",
            "counterexample_text": "",
        },
        "op_000001",
    )
    if legacy_packet.new_problems != []:
        raise RuntimeError(f"legacy prover packet should normalize to empty new_problems, got {legacy_packet.new_problems}")

    current_packet = run_loop.validate_prover_output(
        {
            "problem_id": "op_000001",
            "result": "stuck",
            "proof_sketch": "Need an intermediate lemma.",
            "counterexample_text": "",
            "new_problems": ["a = a", "  ", "Investigate whether left cancellation follows."],
        },
        "op_000001",
    )
    if current_packet.new_problems != ["a = a", "Investigate whether left cancellation follows."]:
        raise RuntimeError(f"unexpected new_problems normalization: {current_packet.new_problems}")

    extra_key_packet = run_loop.validate_prover_output(
        {
            "problem_id": "op_000001",
            "result": "proof",
            "proof_sketch": "Use the previous theorem.",
            "counterexample_text": "",
            "new_problems": ["p", "q", "r"],
            "notes": "extra output should not crash the loop",
        },
        "op_000001",
    )
    if extra_key_packet.new_problems != ["p", "q"]:
        raise RuntimeError(f"unexpected new_problems truncation: {extra_key_packet.new_problems}")

    try:
        run_loop.validate_prover_output(
            {
                "problem_id": "op_000001",
                "result": "stuck",
                "proof_sketch": "",
                "counterexample_text": "",
                "new_problems": ["ok", 1],
            },
            "op_000001",
        )
    except ValueError:
        pass
    else:
        raise RuntimeError("mixed-type new_problems should be rejected")

    try:
        run_loop.validate_prover_output(
            {
                "problem_id": "op_000001",
                "result": "stuck",
                "proof_sketch": "",
            },
            "op_000001",
        )
    except ValueError:
        pass
    else:
        raise RuntimeError("missing required keys should be rejected")

    print("run loop prover contract test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
