from __future__ import annotations

import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))


from plan_derived_compression import validate_plan_output


def _expect_value_error(payload: dict[str, object], *, allowed_kinds: set[str], needle: str) -> None:
    try:
        validate_plan_output(payload, allowed_kinds=allowed_kinds)
    except ValueError as exc:
        if needle not in str(exc):
            raise RuntimeError(f"unexpected error text: {exc}") from exc
        return
    raise RuntimeError("expected ValueError was not raised")


def main() -> int:
    duplicate_payload = {
        "result": "ok",
        "summary": "duplicate-only plan",
        "items": [
            {
                "id": "item_001",
                "kind": "exact_duplicate_collapse",
                "anchor_theorems": ["foo"],
                "rewrite_targets": ["bar"],
                "new_theorems": [],
                "expected_benefit": "collapse duplicate proofs",
            }
        ],
    }
    result, summary, items = validate_plan_output(
        duplicate_payload,
        allowed_kinds={"exact_duplicate_collapse"},
    )
    if result != "ok" or summary != "duplicate-only plan":
        raise RuntimeError("duplicate payload did not validate as expected")
    if len(items) != 1 or items[0]["kind"] != "exact_duplicate_collapse":
        raise RuntimeError(f"unexpected duplicate items: {items}")

    retarget_payload = {
        "result": "ok",
        "summary": "retarget-only plan",
        "items": [
            {
                "id": "item_001",
                "kind": "proof_retarget",
                "anchor_theorems": ["foo"],
                "rewrite_targets": ["bar"],
                "new_theorems": [],
                "expected_benefit": "reuse an existing theorem directly",
            }
        ],
    }
    result, summary, items = validate_plan_output(
        retarget_payload,
        allowed_kinds={"proof_retarget"},
    )
    if result != "ok" or summary != "retarget-only plan":
        raise RuntimeError("retarget payload did not validate as expected")
    if len(items) != 1 or items[0]["kind"] != "proof_retarget":
        raise RuntimeError(f"unexpected retarget items: {items}")

    _expect_value_error(
        retarget_payload,
        allowed_kinds={"exact_duplicate_collapse"},
        needle="not allowed for this pass",
    )

    presentation_payload = {
        "result": "ok",
        "summary": "presentation-only plan",
        "items": [
            {
                "id": "item_001",
                "kind": "cluster_sectionize",
                "anchor_theorems": ["foo"],
                "rewrite_targets": [],
                "new_theorems": [],
                "local_reorder_region": [],
                "section_title": "Local Cluster",
                "section_members": ["foo", "bar"],
                "insert_before": "foo",
                "expected_benefit": "make the cluster easier to scan",
            }
        ],
    }
    result, summary, items = validate_plan_output(
        presentation_payload,
        allowed_kinds={"cluster_sectionize", "cluster_reorder"},
    )
    if result != "ok" or summary != "presentation-only plan":
        raise RuntimeError("presentation payload did not validate as expected")
    if len(items) != 1 or items[0]["kind"] != "cluster_sectionize":
        raise RuntimeError(f"unexpected presentation items: {items}")

    print("derived compression plan validation test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
