---
name: skill-authoring
description: Create or update portable Agent Skills under .agents/skills with concise SKILL.md instructions and optional scripts, references, or assets. Use when a user wants skill-creator behavior that works across Codex, Gemini, Claude Code, OpenCode, or other agents without relying on one vendor's built-in creator.
---

<!-- agent-workbench: managed portable-skill -->

# Skill Authoring

## Dispatch

Use the exact model, effort, delivery boundary, and escalation rule for `skill-authoring` in `AI_AGENT_GUIDE.md`'s **Skill Model and Reasoning Routing** table.

## Workflow

1. Read `.agents/prompts/create-agent-skill.md` if present.
2. If the active environment provides a compatible built-in skill creator, prefer it while keeping the output in the standard project-local format below; otherwise run this portable workflow directly.
3. Gather concrete trigger examples and the repeated task the skill should improve.
4. Create `.agents/skills/<skill-name>/SKILL.md`.
5. Use frontmatter with only `name` and `description` unless a target explicitly requires more.
6. Add `scripts/`, `references/`, or `assets/` only when they materially reduce repeated work or increase reliability.
7. Test scripts and validate frontmatter.

## Quality Bar

Keep skills concise, non-obvious, reusable, project-safe, and actionable.
