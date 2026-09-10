<!-- agent-workbench: managed portable-prompt -->

# Create Agent Skill Prompt

Use this vendor-neutral workflow to create or update a portable Agent Skill that can be adapted for Codex, Gemini, Claude Code, OpenCode, or other agents.

## Canonical Location

Create skills under:

```text
.agents/skills/<skill-name>/SKILL.md
```

Use vendor-specific locations only as optional mirrors. Do not make them the source of truth.

## Skill Naming

- Use lowercase letters, digits, and hyphens only.
- Keep names short, action-oriented, and under 64 characters.
- Match the folder name and the `name:` frontmatter exactly.

## Required SKILL.md Shape

Use only `name` and `description` in frontmatter unless a target vendor explicitly requires more:

```markdown
---
name: <skill-name>
description: <what the skill does and when to use it>
---

# <Human Title>

## Workflow

1. ...
```

The description is the trigger surface. Include the use cases there, not only in the body.

## Workflow

1. Gather concrete examples of user requests that should activate the skill.
2. Decide whether the skill needs only instructions or also `scripts/`, `references/`, or `assets/`.
3. Create the smallest useful skill folder.
4. Keep `SKILL.md` concise and imperative.
5. Put detailed reference material in one-level-deep `references/` files if needed.
6. Test any scripts by running them.
7. Validate that frontmatter is first in the file and includes `name` and `description`.

## Quality Bar

Good skills are:

- Non-obvious or project-specific.
- Actionable with concrete steps.
- Reusable across repeated tasks.
- Small enough to avoid context bloat.
- Safe to keep in the repository.

## Final Response

Report the skill path, intended trigger examples, optional resources added, validation performed, and any vendor-specific mirror that still needs to be generated.
