from __future__ import annotations

import runpy
import sys
from pathlib import Path


TARGET = Path(__file__).resolve().parent / "refactor" / "run_generated_local_passes.py"
TARGET_DIR = str(TARGET.parent)
SCRIPTS_DIR = str(TARGET.parent.parent)

for path in (TARGET_DIR, SCRIPTS_DIR):
    if path not in sys.path:
        sys.path.insert(0, path)


if __name__ == "__main__":
    runpy.run_path(str(TARGET), run_name="__main__")
