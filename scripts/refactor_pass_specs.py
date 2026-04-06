from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class RefactorPassSpec:
    pass_name: str
    cli_description: str
    allowed_kinds: tuple[str, ...]
    allow_repair: bool
    default_input: Path
    default_theory: Path
    default_plan: Path
    default_report: Path
    default_progress_log: Path
    default_planner_prompt: Path
    default_executor_prompt: Path
    default_theorem_reuse_memory: Path


EXACT_DUPLICATE_PASS_SPEC = RefactorPassSpec(
    pass_name="pass_1.2",
    cli_description="Run pass 1.2 exact-duplicate collapse for Derived preview files.",
    allowed_kinds=("exact_duplicate_collapse",),
    allow_repair=True,
    default_input=Path("AutomatedTheoryConstruction/Derived.refactored.preview.lean"),
    default_theory=Path("AutomatedTheoryConstruction/Theory.lean"),
    default_plan=Path("AutomatedTheoryConstruction/Derived.compression.plan.json"),
    default_report=Path("AutomatedTheoryConstruction/Derived.compression.report.json"),
    default_progress_log=Path("AutomatedTheoryConstruction/Derived.compression.executor.log.jsonl"),
    default_planner_prompt=Path("prompts/derived_compression_planner.md"),
    default_executor_prompt=Path("prompts/derived_compression_executor.md"),
    default_theorem_reuse_memory=Path("data/theorem_reuse_memory.json"),
)


PROOF_RETARGET_PASS_SPEC = RefactorPassSpec(
    pass_name="pass_1.3",
    cli_description="Run pass 1.3 proof retargeting for Derived preview files.",
    allowed_kinds=("proof_retarget",),
    allow_repair=True,
    default_input=Path("AutomatedTheoryConstruction/Derived.refactored.preview.lean"),
    default_theory=Path("AutomatedTheoryConstruction/Theory.lean"),
    default_plan=Path("AutomatedTheoryConstruction/Derived.proof_retarget.plan.json"),
    default_report=Path("AutomatedTheoryConstruction/Derived.proof_retarget.report.json"),
    default_progress_log=Path("AutomatedTheoryConstruction/Derived.proof_retarget.executor.log.jsonl"),
    default_planner_prompt=Path("prompts/derived_proof_retarget_planner.md"),
    default_executor_prompt=Path("prompts/derived_compression_executor.md"),
    default_theorem_reuse_memory=Path("data/theorem_reuse_memory.json"),
)


PRESENTATION_PASS_SPEC = RefactorPassSpec(
    pass_name="pass_1.4",
    cli_description="Run pass 1.4 presentation shaping for Derived preview files.",
    allowed_kinds=("cluster_sectionize", "cluster_reorder"),
    allow_repair=False,
    default_input=Path("AutomatedTheoryConstruction/Derived.refactored.preview.lean"),
    default_theory=Path("AutomatedTheoryConstruction/Theory.lean"),
    default_plan=Path("AutomatedTheoryConstruction/Derived.presentation.plan.json"),
    default_report=Path("AutomatedTheoryConstruction/Derived.presentation.report.json"),
    default_progress_log=Path("AutomatedTheoryConstruction/Derived.presentation.executor.log.jsonl"),
    default_planner_prompt=Path("prompts/derived_presentation_planner.md"),
    default_executor_prompt=Path("prompts/derived_presentation_executor.md"),
    default_theorem_reuse_memory=Path("data/theorem_reuse_memory.json"),
)
