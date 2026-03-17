from __future__ import annotations

import json
import os
import urllib.error
import urllib.request
from dataclasses import dataclass
from typing import Any


@dataclass(frozen=True)
class LLMSettings:
    base_url: str
    api_key: str
    model: str
    timeout_sec: int


def load_llm_settings(
    base_url_override: str | None,
    api_key_override: str | None,
    model_override: str | None,
    timeout_override: int | None,
) -> LLMSettings:
    base_url = (base_url_override or os.getenv("ATC_LLM_BASE_URL") or "https://api.openai.com/v1").strip()
    api_key = (api_key_override or os.getenv("ATC_LLM_API_KEY") or "").strip()
    model = (model_override or os.getenv("ATC_LLM_MODEL") or "gpt-4.1-mini").strip()
    timeout_sec = timeout_override if timeout_override is not None else 60

    if not api_key:
        raise ValueError("LLM API key is required. Set --llm-api-key or ATC_LLM_API_KEY.")
    if not base_url:
        raise ValueError("LLM base URL must not be empty.")
    if not model:
        raise ValueError("LLM model must not be empty.")
    if timeout_sec <= 0:
        raise ValueError("LLM timeout must be > 0 seconds.")

    return LLMSettings(base_url=base_url, api_key=api_key, model=model, timeout_sec=timeout_sec)


def _extract_json_object(text: str) -> dict[str, Any]:
    text = text.strip()
    if not text:
        raise ValueError("LLM response is empty")

    try:
        parsed = json.loads(text)
        if isinstance(parsed, dict):
            return parsed
    except json.JSONDecodeError:
        pass

    start = text.find("{")
    end = text.rfind("}")
    if start == -1 or end == -1 or end <= start:
        raise ValueError("LLM response did not contain a JSON object")

    snippet = text[start : end + 1]
    parsed = json.loads(snippet)
    if not isinstance(parsed, dict):
        raise ValueError("LLM JSON payload must be an object")
    return parsed


def call_chat_completion_json(settings: LLMSettings, system_prompt: str, user_payload: dict[str, Any]) -> dict[str, Any]:
    url = settings.base_url.rstrip("/") + "/chat/completions"
    request_payload = {
        "model": settings.model,
        "temperature": 0,
        "messages": [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": json.dumps(user_payload, ensure_ascii=False)},
        ],
    }

    data = json.dumps(request_payload).encode("utf-8")
    request = urllib.request.Request(
        url=url,
        data=data,
        method="POST",
        headers={
            "Content-Type": "application/json",
            "Accept": "application/json",
            "User-Agent": "atc-prototype/0.1",
            "Authorization": f"Bearer {settings.api_key}",
        },
    )

    try:
        with urllib.request.urlopen(request, timeout=settings.timeout_sec) as response:
            raw = response.read().decode("utf-8")
    except urllib.error.HTTPError as exc:
        body = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"LLM HTTP error {exc.code}: {body}") from exc
    except urllib.error.URLError as exc:
        raise RuntimeError(f"LLM connection failed: {exc}") from exc

    result = json.loads(raw)
    choices = result.get("choices", [])
    if not choices:
        raise RuntimeError("LLM response did not contain choices")

    content = choices[0].get("message", {}).get("content", "")
    if not isinstance(content, str):
        raise RuntimeError("LLM response content is not a string")

    return _extract_json_object(content)
