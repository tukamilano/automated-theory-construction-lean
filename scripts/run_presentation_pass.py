from __future__ import annotations

from refactor_pass_runner import run_refactor_pass_cli
from refactor_pass_specs import PRESENTATION_PASS_SPEC


if __name__ == "__main__":
    run_refactor_pass_cli(PRESENTATION_PASS_SPEC)
