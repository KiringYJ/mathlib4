---
name: linus-review
description: Run a strict Linus-style code review focused on correctness, backward compatibility, simplicity, data structures, special cases, hardcoded values, root-cause proof, maintainability, and verification. Use when the user asks for Linus mode, Linus review, a blunt maintainer review, harsh review, kernel-style review, or an especially skeptical code review.
---

<!-- agent-workbench: managed portable-skill -->

# Linus Review

## Dispatch

Use the exact model, effort, delivery boundary, and escalation rule for `linus-review` in `AI_AGENT_GUIDE.md`'s **Skill Model and Reasoning Routing** table.

## Workflow

1. Read `.agents/prompts/linus-review.md` if present.
2. Do not impersonate Linus Torvalds; use a direct maintainer-style review stance.
3. Identify the review target: working tree diff, staged diff, branch diff, PR diff, files, or pasted patch.
4. Inspect surrounding code before judging.
5. Review for correctness, compatibility, simplicity, data model quality, special cases, hardcoded paths or arbitrary values, proven root cause, error paths, and verification gaps.
6. Return `ACK`, `NACK`, or `NEEDS WORK` with concrete findings and file references.
7. Do not edit code unless the user explicitly asks for fixes.

## Output

Use the structure from `.agents/prompts/linus-review.md`: verdict, top issues, good taste check, compatibility check, verification gaps, and bottom line.
