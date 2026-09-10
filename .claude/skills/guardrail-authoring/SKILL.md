---
name: guardrail-authoring
description: Create or update vendor-neutral project guardrails under .agents/guardrails and optionally generate thin Claude, Codex, or Gemini hook/config adapters. Use when a user wants hookify-like behavior, safety rules, tool-use constraints, or repeatable enforcement without making a vendor-specific hook format the source of truth.
---

<!-- agent-workbench: managed portable-skill -->

# Guardrail Authoring

## Dispatch

Use the exact model, effort, delivery boundary, and escalation rule for `guardrail-authoring` in `AI_AGENT_GUIDE.md`'s **Skill Model and Reasoning Routing** table.

## Workflow

1. Read `.agents/prompts/create-guardrail.md` if present.
2. Capture the rule intent, trigger pattern, decision, and remediation message.
3. Write the canonical rule to `.agents/guardrails/<slug>.md`.
4. Generate vendor-specific hook/config adapters only when explicitly requested.
5. Validate any generated JSON, TOML, shell, PowerShell, Python, or JavaScript.

## Guardrails

- Prefer guidance when enforcement is not deterministic.
- Keep executable hooks project-local.
- Do not install global hooks or marketplace plugins.
