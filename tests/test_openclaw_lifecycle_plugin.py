"""BDD contract tests for the native OpenClaw lifecycle controller package."""

from __future__ import annotations

import json
from pathlib import Path

PLUGIN = Path(__file__).parents[1] / "integrations" / "openclaw-lifecycle-plugin"


def test_given_a_native_plugin_when_packaged_then_manifest_and_runtime_entry_agree() -> None:
    package = json.loads((PLUGIN / "package.json").read_text(encoding="utf-8"))
    manifest = json.loads((PLUGIN / "openclaw.plugin.json").read_text(encoding="utf-8"))

    assert manifest["id"] == "collatz-lifecycle"
    assert package["openclaw"]["extensions"] == ["./index.js"]
    assert manifest["configSchema"]["required"] == ["projectRoot"]


def test_given_an_openclaw_turn_when_the_controller_loads_then_all_receipt_hooks_exist() -> None:
    source = (PLUGIN / "index.js").read_text(encoding="utf-8")

    for hook in ("before_agent_run", "before_tool_call", "after_tool_call", "agent_end"):
        assert f'api.on("{hook}"' in source
    assert '"begin-operation"' in source
    assert '"finish-operation"' in source
    assert '"consume"' in source
