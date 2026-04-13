from __future__ import annotations

import json
import sys
from pathlib import Path
from types import SimpleNamespace


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))


import worker_client


def main() -> int:
    original_run = worker_client.subprocess.run
    seen: dict[str, object] = {}

    def fake_run(cmd, *, input, capture_output, text, timeout, env, check):
        seen["cmd"] = cmd
        seen["timeout"] = timeout
        seen["formalize_timeout"] = env.get("ATC_FORMALIZE_WORKER_TIMEOUT")
        seen["formalize_codex_timeout"] = env.get("ATC_FORMALIZE_CODEX_TIMEOUT")
        return SimpleNamespace(returncode=0, stdout=json.dumps({"result_payload": {"ok": True}}), stderr="")

    worker_client.subprocess.run = fake_run
    try:
        settings = worker_client.WorkerSettings(
            command="dummy-worker",
            timeout_sec=1800,
            propagate_timeout=True,
            codex_timeout_sec=1800,
            propagate_codex_timeout=True,
        )
        payload, _ = worker_client.invoke_worker_json(
            settings=settings,
            task_type="formalize",
            system_prompt="prompt",
            payload={"x": 1},
        )
    finally:
        worker_client.subprocess.run = original_run

    if payload != {"ok": True}:
        raise RuntimeError(f"unexpected payload: {payload}")
    if seen.get("timeout") != 1800:
        raise RuntimeError(f"expected outer timeout 1800, got {seen.get('timeout')}")
    if seen.get("formalize_timeout") != "1800":
        raise RuntimeError(f"expected ATC_FORMALIZE_WORKER_TIMEOUT=1800, got {seen.get('formalize_timeout')}")
    if seen.get("formalize_codex_timeout") != "1800":
        raise RuntimeError(
            f"expected ATC_FORMALIZE_CODEX_TIMEOUT=1800, got {seen.get('formalize_codex_timeout')}"
        )

    original_problem_design_worker_timeout = worker_client.os.environ.get("ATC_PROBLEM_DESIGN_CLUSTER_WORKER_TIMEOUT")
    original_problem_design_codex_timeout = worker_client.os.environ.get("ATC_PROBLEM_DESIGN_CLUSTER_CODEX_TIMEOUT")
    seen_problem_design: dict[str, object] = {}

    def fake_run_problem_design(cmd, *, input, capture_output, text, timeout, env, check):
        seen_problem_design["timeout"] = timeout
        seen_problem_design["problem_design_timeout"] = env.get("ATC_PROBLEM_DESIGN_CLUSTER_WORKER_TIMEOUT")
        seen_problem_design["problem_design_codex_timeout"] = env.get("ATC_PROBLEM_DESIGN_CLUSTER_CODEX_TIMEOUT")
        return SimpleNamespace(returncode=0, stdout=json.dumps({"result_payload": {"ok": True}}), stderr="")

    worker_client.subprocess.run = fake_run_problem_design
    try:
        worker_client.os.environ["ATC_PROBLEM_DESIGN_CLUSTER_WORKER_TIMEOUT"] = "0"
        worker_client.os.environ["ATC_PROBLEM_DESIGN_CLUSTER_CODEX_TIMEOUT"] = "0"
        payload, _ = worker_client.invoke_worker_json(
            settings=settings,
            task_type="problem_design_cluster",
            system_prompt="prompt",
            payload={"x": 1},
        )
    finally:
        if original_problem_design_worker_timeout is None:
            worker_client.os.environ.pop("ATC_PROBLEM_DESIGN_CLUSTER_WORKER_TIMEOUT", None)
        else:
            worker_client.os.environ["ATC_PROBLEM_DESIGN_CLUSTER_WORKER_TIMEOUT"] = original_problem_design_worker_timeout
        if original_problem_design_codex_timeout is None:
            worker_client.os.environ.pop("ATC_PROBLEM_DESIGN_CLUSTER_CODEX_TIMEOUT", None)
        else:
            worker_client.os.environ["ATC_PROBLEM_DESIGN_CLUSTER_CODEX_TIMEOUT"] = original_problem_design_codex_timeout
        worker_client.subprocess.run = original_run

    if payload != {"ok": True}:
        raise RuntimeError(f"unexpected problem_design payload: {payload}")
    if seen_problem_design.get("timeout") is not None:
        raise RuntimeError(f"expected unbounded timeout, got {seen_problem_design.get('timeout')}")
    if seen_problem_design.get("problem_design_timeout") != "0":
        raise RuntimeError(
            "expected ATC_PROBLEM_DESIGN_CLUSTER_WORKER_TIMEOUT=0, "
            f"got {seen_problem_design.get('problem_design_timeout')}"
        )
    if seen_problem_design.get("problem_design_codex_timeout") != "0":
        raise RuntimeError(
            "expected ATC_PROBLEM_DESIGN_CLUSTER_CODEX_TIMEOUT=0, "
            f"got {seen_problem_design.get('problem_design_codex_timeout')}"
        )

    print("worker client main theorem timeout test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
