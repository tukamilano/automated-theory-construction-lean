from __future__ import annotations

from refactor_pass_runner import run_refactor_pass_cli
from refactor_pass_specs import PROOF_RETARGET_PASS_SPEC


if __name__ == "__main__":
    run_refactor_pass_cli(PROOF_RETARGET_PASS_SPEC)
