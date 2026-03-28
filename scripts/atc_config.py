from __future__ import annotations

import json
import os
from dataclasses import asdict, dataclass, field, is_dataclass
from pathlib import Path
from typing import Any
from typing import Iterable


REPO_ROOT = Path(__file__).resolve().parent.parent
TASK_NAMES = (
    "prover",
    "prover_statement",
    "formalize",
    "repair",
    "prioritize_open_problems",
    "refactor_derived",
)

_MISSING = object()


@dataclass
class PathsConfig:
    theory_file: Path
    derived_file: Path
    scratch_file: Path
    seeds_file: Path
    preview_file: Path
    reviewed_file: Path
    data_dir: Path
    prompt_dir: Path
    log_dir: Path
    theorem_reuse_memory_file: Path


@dataclass
class WorkerTaskConfig:
    command: str | None = None
    timeout: int | None = None
    codex_model: str | None = None
    codex_timeout: int | None = None


@dataclass
class WorkerConfig:
    command: str | None = None
    timeout: int | None = None
    codex_model: str | None = None
    codex_timeout: int | None = None
    tasks: dict[str, WorkerTaskConfig] = field(default_factory=dict)


@dataclass
class RuntimeConfig:
    initialize_on_start: bool = True
    phase_logs: bool = True
    open_problem_failure_threshold: int = 2
    priority_refresh_theorem_interval: int = 5
    main_theorem_interval: int = 0
    main_theorem_formalize_worker_timeout: int | None = None
    main_theorem_repair_worker_timeout: int | None = None
    main_theorem_verify_timeout: int = 600
    main_theorem_formalization_retry_budget_sec: int = 3600


@dataclass
class LoggingConfig:
    console_level: str = "info"
    console_format: str = "pretty"
    persist_events: bool = True
    persist_summary: bool = True
    persist_worker_raw: bool = False


@dataclass
class AppConfig:
    repo_root: Path
    config_path: Path | None
    paths: PathsConfig
    worker: WorkerConfig
    runtime: RuntimeConfig
    logging: LoggingConfig


def _nested_get(data: dict[str, Any], *keys: str) -> Any:
    current: Any = data
    for key in keys:
        if not isinstance(current, dict) or key not in current:
            return _MISSING
        current = current[key]
    return current


def _find_config_path(explicit: str | None) -> Path | None:
    if explicit is not None:
        candidate = Path(explicit)
        return candidate.resolve() if candidate.is_absolute() else (Path.cwd() / candidate).resolve()

    for candidate in (REPO_ROOT / "atc.json", REPO_ROOT / "atc.toml"):
        if candidate.exists():
            return candidate
    return None


def _load_toml_module() -> Any:
    try:
        import tomllib  # type: ignore

        return tomllib
    except ModuleNotFoundError:
        try:
            import tomli as tomllib  # type: ignore

            return tomllib
        except ModuleNotFoundError as exc:
            raise RuntimeError(
                "TOML config requires Python 3.11+ (`tomllib`) or the `tomli` package. "
                "Use a JSON config file such as `atc.json` if you want zero extra dependencies."
            ) from exc


def _load_config_data(config_path: Path | None) -> dict[str, Any]:
    if config_path is None:
        return {}
    if not config_path.exists():
        raise ValueError(f"Config file not found: {config_path}")

    suffix = config_path.suffix.lower()
    if suffix == ".json":
        with config_path.open("r", encoding="utf-8") as handle:
            data = json.load(handle)
    elif suffix == ".toml":
        tomllib = _load_toml_module()
        with config_path.open("rb") as handle:
            data = tomllib.load(handle)
    else:
        raise ValueError(
            f"Unsupported config format: {config_path}. Use .json or .toml."
        )

    if not isinstance(data, dict):
        raise ValueError(f"Config file must contain a top-level object/table: {config_path}")
    return data


def _resolve_path(raw: str | Path, *, base_dir: Path) -> Path:
    path = raw if isinstance(raw, Path) else Path(raw)
    return path.resolve() if path.is_absolute() else (base_dir / path).resolve()


def _coerce_optional_str(raw: Any, *, label: str) -> str | None:
    if raw is None:
        return None
    text = str(raw).strip()
    if not text:
        return None
    return text


def _coerce_int(raw: Any, *, label: str, minimum: int | None = None) -> int:
    value = int(raw)
    if minimum is not None and value < minimum:
        raise ValueError(f"{label} must be >= {minimum}")
    return value


def _coerce_optional_int(raw: Any, *, label: str, minimum: int | None = None) -> int | None:
    if raw is None:
        return None
    return _coerce_int(raw, label=label, minimum=minimum)


def _coerce_bool(raw: Any, *, label: str) -> bool:
    if isinstance(raw, bool):
        return raw
    if isinstance(raw, str):
        normalized = raw.strip().lower()
        if normalized in {"1", "true", "yes", "on"}:
            return True
        if normalized in {"0", "false", "no", "off"}:
            return False
    raise ValueError(f"{label} must be a boolean")


def _coerce_optional_bool(raw: Any, *, label: str) -> bool | None:
    if raw is None:
        return None
    return _coerce_bool(raw, label=label)


def _resolve_raw(
    *,
    cli_value: Any = None,
    env_names: tuple[str, ...] = (),
    file_value: Any = _MISSING,
    default: Any = _MISSING,
    env: dict[str, str],
    label: str,
) -> tuple[Any, str, str]:
    if cli_value is not None:
        return cli_value, f"cli:{label}", "cli"
    for env_name in env_names:
        env_value = env.get(env_name)
        if env_value is not None and env_value != "":
            return env_value, f"env:{env_name}", "env"
    if file_value is not _MISSING:
        return file_value, f"config:{label}", "config"
    if default is _MISSING:
        return None, "default", "default"
    return default, "default", "default"


def _cli_value(args: Any, *names: str) -> Any:
    for name in names:
        if hasattr(args, name):
            value = getattr(args, name)
            if value is not None:
                return value
    return None


def load_app_config(args: Any) -> tuple[AppConfig, dict[str, str]]:
    env = dict(os.environ)
    config_path = _find_config_path(getattr(args, "config", None))
    config_data = _load_config_data(config_path)
    config_base_dir = config_path.parent if config_path is not None else REPO_ROOT
    cwd_base_dir = Path.cwd()
    sources: dict[str, str] = {}

    def choose_path(*, cli_names: tuple[str, ...], file_keys: tuple[str, ...], default: str, label: str) -> Path:
        raw, source, source_kind = _resolve_raw(
            cli_value=_cli_value(args, *cli_names),
            file_value=_nested_get(config_data, *file_keys),
            default=default,
            env=env,
            label=label,
        )
        base_dir = cwd_base_dir if source_kind == "cli" else config_base_dir if source_kind == "config" else REPO_ROOT
        value = _resolve_path(raw, base_dir=base_dir)
        sources[label] = source
        return value

    def choose_str(
        *,
        cli_names: tuple[str, ...] = (),
        env_names: tuple[str, ...] = (),
        file_keys: tuple[str, ...],
        default: str | None = None,
        label: str,
    ) -> str | None:
        raw, source, _ = _resolve_raw(
            cli_value=_cli_value(args, *cli_names),
            env_names=env_names,
            file_value=_nested_get(config_data, *file_keys),
            default=default,
            env=env,
            label=label,
        )
        value = _coerce_optional_str(raw, label=label)
        sources[label] = source
        return value

    def choose_int(
        *,
        cli_names: tuple[str, ...] = (),
        env_names: tuple[str, ...] = (),
        file_keys: tuple[str, ...],
        default: int | None = None,
        minimum: int | None = None,
        label: str,
    ) -> int | None:
        raw, source, _ = _resolve_raw(
            cli_value=_cli_value(args, *cli_names),
            env_names=env_names,
            file_value=_nested_get(config_data, *file_keys),
            default=default,
            env=env,
            label=label,
        )
        value = _coerce_optional_int(raw, label=label, minimum=minimum)
        sources[label] = source
        return value

    def choose_bool(
        *,
        cli_names: tuple[str, ...] = (),
        env_names: tuple[str, ...] = (),
        file_keys: tuple[str, ...],
        default: bool | None = None,
        label: str,
    ) -> bool | None:
        raw, source, _ = _resolve_raw(
            cli_value=_cli_value(args, *cli_names),
            env_names=env_names,
            file_value=_nested_get(config_data, *file_keys),
            default=default,
            env=env,
            label=label,
        )
        value = _coerce_optional_bool(raw, label=label)
        sources[label] = source
        return value

    paths = PathsConfig(
        theory_file=choose_path(
            cli_names=("theory_file",),
            file_keys=("paths", "theory_file"),
            default="AutomatedTheoryConstruction/Theory.lean",
            label="paths.theory_file",
        ),
        derived_file=choose_path(
            cli_names=("derived_file",),
            file_keys=("paths", "derived_file"),
            default="AutomatedTheoryConstruction/Derived.lean",
            label="paths.derived_file",
        ),
        scratch_file=choose_path(
            cli_names=("scratch_file",),
            file_keys=("paths", "scratch_file"),
            default="AutomatedTheoryConstruction/Scratch.lean",
            label="paths.scratch_file",
        ),
        seeds_file=choose_path(
            cli_names=("seeds_file",),
            file_keys=("paths", "seeds_file"),
            default="AutomatedTheoryConstruction/seeds.jsonl",
            label="paths.seeds_file",
        ),
        preview_file=choose_path(
            cli_names=("preview_file",),
            file_keys=("paths", "preview_file"),
            default="AutomatedTheoryConstruction/Derived.refactored.preview.lean",
            label="paths.preview_file",
        ),
        reviewed_file=choose_path(
            cli_names=("review_output_file", "reviewed_file"),
            file_keys=("paths", "reviewed_file"),
            default="AutomatedTheoryConstruction/Derived.refactored.reviewed.lean",
            label="paths.reviewed_file",
        ),
        data_dir=choose_path(
            cli_names=("data_dir",),
            file_keys=("paths", "data_dir"),
            default="data",
            label="paths.data_dir",
        ),
        prompt_dir=choose_path(
            cli_names=("prompt_dir",),
            file_keys=("paths", "prompt_dir"),
            default="prompts",
            label="paths.prompt_dir",
        ),
        log_dir=choose_path(
            cli_names=("log_dir",),
            file_keys=("paths", "log_dir"),
            default="data/runs",
            label="paths.log_dir",
        ),
        theorem_reuse_memory_file=choose_path(
            cli_names=("theorem_reuse_memory_file",),
            file_keys=("paths", "theorem_reuse_memory_file"),
            default="data/theorem_reuse_memory.json",
            label="paths.theorem_reuse_memory_file",
        ),
    )

    task_configs: dict[str, WorkerTaskConfig] = {}
    for task_name in TASK_NAMES:
        task_upper = task_name.upper()
        cli_prefix = task_name if task_name != "prioritize_open_problems" else "prioritize_open_problems"
        if task_name == "refactor_derived":
            cli_command_names = ("refactor_worker_command",)
            cli_timeout_names = ("refactor_worker_timeout",)
            cli_model_names = ("refactor_codex_model",)
            cli_codex_timeout_names = ("refactor_codex_timeout",)
        else:
            cli_command_names = (f"{cli_prefix}_worker_command",)
            cli_timeout_names = (f"{cli_prefix}_worker_timeout",)
            cli_model_names = (f"{cli_prefix}_codex_model",)
            cli_codex_timeout_names = (f"{cli_prefix}_codex_timeout",)
        task_configs[task_name] = WorkerTaskConfig(
            command=choose_str(
                cli_names=cli_command_names,
                env_names=(f"ATC_{task_upper}_WORKER_COMMAND",),
                file_keys=("worker", "tasks", task_name, "command"),
                default=None,
                label=f"worker.tasks.{task_name}.command",
            ),
            timeout=choose_int(
                cli_names=cli_timeout_names,
                env_names=(f"ATC_{task_upper}_WORKER_TIMEOUT",),
                file_keys=("worker", "tasks", task_name, "timeout"),
                default=None,
                minimum=0,
                label=f"worker.tasks.{task_name}.timeout",
            ),
            codex_model=choose_str(
                cli_names=cli_model_names,
                env_names=(f"ATC_{task_upper}_CODEX_MODEL",),
                file_keys=("worker", "tasks", task_name, "codex_model"),
                default=None,
                label=f"worker.tasks.{task_name}.codex_model",
            ),
            codex_timeout=choose_int(
                cli_names=cli_codex_timeout_names,
                env_names=(f"ATC_{task_upper}_CODEX_TIMEOUT",),
                file_keys=("worker", "tasks", task_name, "codex_timeout"),
                default=None,
                minimum=0,
                label=f"worker.tasks.{task_name}.codex_timeout",
            ),
        )

    worker = WorkerConfig(
        command=choose_str(
            cli_names=("worker_command",),
            env_names=("ATC_WORKER_COMMAND",),
            file_keys=("worker", "command"),
            default=None,
            label="worker.command",
        ),
        timeout=choose_int(
            cli_names=("worker_timeout",),
            env_names=("ATC_WORKER_TIMEOUT",),
            file_keys=("worker", "timeout"),
            default=None,
            minimum=0,
            label="worker.timeout",
        ),
        codex_model=choose_str(
            cli_names=("codex_model",),
            env_names=("ATC_CODEX_MODEL",),
            file_keys=("worker", "codex_model"),
            default=None,
            label="worker.codex_model",
        ),
        codex_timeout=choose_int(
            cli_names=("codex_timeout",),
            env_names=("ATC_CODEX_TIMEOUT",),
            file_keys=("worker", "codex_timeout"),
            default=None,
            minimum=0,
            label="worker.codex_timeout",
        ),
        tasks=task_configs,
    )

    runtime = RuntimeConfig(
        initialize_on_start=bool(
            choose_bool(
                cli_names=("initialize_on_start",),
                file_keys=("runtime", "initialize_on_start"),
                default=True,
                label="runtime.initialize_on_start",
            )
        ),
        phase_logs=bool(
            choose_bool(
                cli_names=("phase_logs",),
                file_keys=("runtime", "phase_logs"),
                default=True,
                label="runtime.phase_logs",
            )
        ),
        open_problem_failure_threshold=int(
            choose_int(
                cli_names=("open_problem_failure_threshold",),
                file_keys=("runtime", "open_problem_failure_threshold"),
                default=2,
                minimum=0,
                label="runtime.open_problem_failure_threshold",
            )
        ),
        priority_refresh_theorem_interval=int(
            choose_int(
                cli_names=("priority_refresh_theorem_interval",),
                file_keys=("runtime", "priority_refresh_theorem_interval"),
                default=5,
                minimum=0,
                label="runtime.priority_refresh_theorem_interval",
            )
        ),
        main_theorem_interval=int(
            choose_int(
                cli_names=("main_theorem_interval",),
                file_keys=("runtime", "main_theorem_interval"),
                default=0,
                minimum=0,
                label="runtime.main_theorem_interval",
            )
        ),
        main_theorem_formalize_worker_timeout=choose_int(
            cli_names=("main_theorem_formalize_worker_timeout",),
            file_keys=("runtime", "main_theorem_formalize_worker_timeout"),
            default=None,
            minimum=0,
            label="runtime.main_theorem_formalize_worker_timeout",
        ),
        main_theorem_repair_worker_timeout=choose_int(
            cli_names=("main_theorem_repair_worker_timeout",),
            file_keys=("runtime", "main_theorem_repair_worker_timeout"),
            default=None,
            minimum=0,
            label="runtime.main_theorem_repair_worker_timeout",
        ),
        main_theorem_verify_timeout=int(
            choose_int(
                cli_names=("main_theorem_verify_timeout",),
                file_keys=("runtime", "main_theorem_verify_timeout"),
                default=600,
                minimum=0,
                label="runtime.main_theorem_verify_timeout",
            )
        ),
        main_theorem_formalization_retry_budget_sec=int(
            choose_int(
                cli_names=("main_theorem_formalization_retry_budget_sec",),
                file_keys=("runtime", "main_theorem_formalization_retry_budget_sec"),
                default=3600,
                minimum=0,
                label="runtime.main_theorem_formalization_retry_budget_sec",
            )
        ),
    )

    logging = LoggingConfig(
        console_level=choose_str(
            cli_names=("log_level",),
            file_keys=("logging", "console_level"),
            default="info",
            label="logging.console_level",
        )
        or "info",
        console_format=choose_str(
            cli_names=("log_format",),
            file_keys=("logging", "console_format"),
            default="pretty",
            label="logging.console_format",
        )
        or "pretty",
        persist_events=bool(
            choose_bool(
                cli_names=("persist_events",),
                file_keys=("logging", "persist_events"),
                default=True,
                label="logging.persist_events",
            )
        ),
        persist_summary=bool(
            choose_bool(
                cli_names=("persist_summary",),
                file_keys=("logging", "persist_summary"),
                default=True,
                label="logging.persist_summary",
            )
        ),
        persist_worker_raw=bool(
            choose_bool(
                cli_names=("log_worker_raw",),
                file_keys=("logging", "persist_worker_raw"),
                default=False,
                label="logging.persist_worker_raw",
            )
        ),
    )

    return (
        AppConfig(
            repo_root=REPO_ROOT,
            config_path=config_path,
            paths=paths,
            worker=worker,
            runtime=runtime,
            logging=logging,
        ),
        sources,
    )


def _json_ready(value: Any) -> Any:
    if isinstance(value, Path):
        return str(value)
    if is_dataclass(value):
        return {key: _json_ready(item) for key, item in asdict(value).items()}
    if isinstance(value, dict):
        return {str(key): _json_ready(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [_json_ready(item) for item in value]
    return value


def app_config_to_dict(config: AppConfig) -> dict[str, Any]:
    return _json_ready(config)


def app_config_to_json(config: AppConfig, sources: dict[str, str]) -> str:
    payload = {
        "config_path": None if config.config_path is None else str(config.config_path),
        "resolved": app_config_to_dict(config),
        "sources": dict(sorted(sources.items())),
    }
    return json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True)


def build_worker_env(config: AppConfig, *, task_names: Iterable[str] = TASK_NAMES) -> dict[str, str]:
    env_updates: dict[str, str] = {}

    def put(key: str, value: str | int | None) -> None:
        if value is None:
            return
        env_updates[key] = str(value)

    put("ATC_WORKER_COMMAND", config.worker.command)
    put("ATC_WORKER_TIMEOUT", config.worker.timeout)
    put("ATC_CODEX_MODEL", config.worker.codex_model)
    put("ATC_CODEX_TIMEOUT", config.worker.codex_timeout)

    for task_name in task_names:
        task = config.worker.tasks.get(task_name)
        if task is None:
            continue
        prefix = f"ATC_{task_name.upper()}"
        put(f"{prefix}_WORKER_COMMAND", task.command)
        put(f"{prefix}_WORKER_TIMEOUT", task.timeout)
        put(f"{prefix}_CODEX_MODEL", task.codex_model)
        put(f"{prefix}_CODEX_TIMEOUT", task.codex_timeout)

    return env_updates
