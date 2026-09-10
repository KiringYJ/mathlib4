<!-- agent-workbench: managed portable-prompt -->

# Create Guardrail Prompt

Use this vendor-neutral workflow to turn a safety, quality, or workflow rule into a reusable project-local guardrail. It replaces tool-specific hookify behavior with canonical markdown rules and optional thin adapters.

## Output Locations

- Canonical guardrail: `.agents/guardrails/<slug>.md`
- Optional adapters, only when explicitly requested:
  - Claude Code hooks/settings under `.claude/`
  - Codex hooks/config under `.codex/` or project hook config
  - Gemini hooks/settings under `.gemini/`

Do not install global hooks, marketplace plugins, or user-scope configuration.

## Workflow

1. Identify the behavior to prevent, require, or warn about.
2. Decide whether the rule should be:
   - **Guidance only**: written instruction in `AI_AGENT_GUIDE.md` or `AI_AGENT_PROJECT.md`.
   - **Guardrail document**: reusable rule under `.agents/guardrails/`.
   - **Executable hook**: project-local script/config, only when deterministic enforcement is needed.
3. Create or update `.agents/guardrails/<slug>.md`.
4. If an adapter is requested, generate the thinnest possible adapter that points to the canonical rule.
5. Verify syntax for any generated JSON, TOML, shell, PowerShell, Python, or JavaScript.

## Guardrail Template

```markdown
# <Guardrail Name>

## Intent

What this rule protects.

## Applies When

- Tool, file, command, or workflow pattern that triggers the rule.

## Decision

- Allow, warn, block, or require confirmation.

## Message to Agent

Concise remediation instructions.

## Examples

- Blocked: `<bad example>`
- Allowed: `<good example>`

## Vendor Adapter Notes

- Claude:
- Codex:
- Gemini:
```

## Final Response

Report the canonical guardrail path, any adapter files created, validation performed, and remaining manual wiring required.
