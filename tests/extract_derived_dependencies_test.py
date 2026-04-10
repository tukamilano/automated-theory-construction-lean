from __future__ import annotations

import json
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))


from extract_derived_dependencies import _build_harness_source
from extract_derived_dependencies import _normalize_dependency_payload


def main() -> int:
    harness = _build_harness_source(
        derived_import="AutomatedTheoryConstruction.Derived",
        extractor_source="import Lean\n\ndef dummy : Nat := 0\n",
        declaration_names=[
            "AutomatedTheoryConstruction.alpha",
            "AutomatedTheoryConstruction.beta",
        ],
        output_file=Path("/tmp/out.json"),
        depth=1,
    )
    if "import AutomatedTheoryConstruction.Derived" not in harness:
        raise RuntimeError("missing derived import in harness")
    if "`AutomatedTheoryConstruction.alpha" not in harness or "`AutomatedTheoryConstruction.beta" not in harness:
        raise RuntimeError("missing declaration names in harness")
    if 'writeJsonToFile "/tmp/out.json"' not in harness:
        raise RuntimeError("missing output path in harness")

    output_file = Path("/tmp/extract-derived-deps-test.json")
    rows = _normalize_dependency_payload(
        [
            {
                "name": "AutomatedTheoryConstruction.alpha",
                "constCategory": "Theorem",
                "constType": "True",
                "references": ["Trans.trans", "AutomatedTheoryConstruction.beta"],
            },
            {
                "name": "AutomatedTheoryConstruction.beta",
                "constCategory": "Theorem",
                "constType": "True",
                "references": [],
            },
        ],
        declaration_names=[
            "AutomatedTheoryConstruction.alpha",
            "AutomatedTheoryConstruction.beta",
        ],
        output_file=output_file,
    )
    if [row["name"] for row in rows] != [
        "AutomatedTheoryConstruction.alpha",
        "AutomatedTheoryConstruction.beta",
    ]:
        raise RuntimeError(f"unexpected row ordering: {rows}")
    persisted = json.loads(output_file.read_text(encoding="utf-8"))
    if len(persisted) != 2 or persisted[0]["references"][0] != "Trans.trans":
        raise RuntimeError(f"unexpected persisted payload: {persisted}")
    output_file.unlink(missing_ok=True)

    print("extract derived dependencies test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
