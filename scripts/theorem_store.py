from __future__ import annotations

from pathlib import Path


NAMESPACE_MARKER = "namespace AutomatedTheoryConstruction"
END_MARKER = "end AutomatedTheoryConstruction"

PRODUCT_TEMPLATE = (
    "import Mathlib\n"
    "import AutomatedTheoryConstruction.Theory\n\n"
    "set_option autoImplicit false\n\n"
    "namespace AutomatedTheoryConstruction\n\n"
    "-- Stable reviewed theorems live here.\n"
    "-- Promote staging results from Derived.lean into this file when they are ready.\n\n"
    "end AutomatedTheoryConstruction\n"
)

DERIVED_TEMPLATE = (
    "import Mathlib\n"
    "import AutomatedTheoryConstruction.Theory\n"
    "import AutomatedTheoryConstruction.Product\n\n"
    "set_option autoImplicit false\n\n"
    "namespace AutomatedTheoryConstruction\n\n"
    "-- Newly verified staging theorems are appended here by scripts/append_derived.py.\n"
    "-- Promote reviewed results into Product.lean and then reset this file.\n\n"
    "end AutomatedTheoryConstruction\n"
)


def product_file_for_derived(derived_file: Path) -> Path:
    return derived_file.with_name("Product.lean")


def extract_module_body(module_text: str) -> str:
    start = module_text.find(NAMESPACE_MARKER)
    end = module_text.rfind(END_MARKER)
    if start < 0 or end < 0 or end <= start:
        raise ValueError("module is missing namespace/end markers")
    body = module_text[start + len(NAMESPACE_MARKER) : end].strip()
    return body


def ensure_product_file(product_file: Path) -> None:
    if product_file.exists():
        return
    product_file.parent.mkdir(parents=True, exist_ok=True)
    product_file.write_text(PRODUCT_TEMPLATE, encoding="utf-8")


def render_promoted_product(*, existing_product_text: str, staged_text: str) -> str:
    product_body = extract_module_body(existing_product_text)
    staged_body = extract_module_body(staged_text)
    sections = [section for section in (product_body, staged_body) if section.strip()]
    merged_body = "\n\n".join(sections).strip()
    prefix, _, _ = existing_product_text.partition(NAMESPACE_MARKER)
    return (
        prefix
        + NAMESPACE_MARKER
        + "\n\n"
        + (merged_body + "\n\n" if merged_body else "")
        + END_MARKER
        + "\n"
    )
