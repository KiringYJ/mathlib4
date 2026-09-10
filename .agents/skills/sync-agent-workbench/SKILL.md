---
name: sync-agent-workbench
description: Synchronize, audit, or repair composable agent-workbench policy in a project. Use when a user wants canonical AI_AGENT_GUIDE.md, thin vendor loader entrypoints, project-selected profiles, portable prompts, and standard Agent Skills without depending on a marketplace, plugin, global config, or submodule.
---

<!-- agent-workbench: managed portable-skill -->

# Sync Agent Workbench

## Dispatch

Use the exact model, effort, delivery boundary, and escalation rule for `sync-agent-workbench` in `AI_AGENT_GUIDE.md`'s **Skill Model and Reasoning Routing** table.

## Workflow

1. Read `AI_AGENT_GUIDE.md` and `AI_AGENT_PROJECT.md` if present.
2. Choose the requested workflow:
   - Sync: follow `.agents/prompts/sync-agent-workbench.md` when present, otherwise use the upstream `prompts/sync-agent-workbench.md`.
   - Audit: follow `.agents/prompts/audit-agent-workbench.md` when present.
   - Repair: follow `.agents/prompts/repair-agent-workbench.md` when present.
3. Modify only the files allowed by the selected prompt.
4. Keep `AI_AGENT_PROJECT.md` manual after initial creation.
5. Keep vendor entrypoints thin and canonical content under `AI_AGENT_GUIDE.md`, `.agents/prompts/`, and `.agents/skills/`.
6. Use `.agents/skills/` as the shared skill tree. When the Claude target is enabled, copy the registered managed source/resource set to `.claude/skills/` for discovery and keep corresponding managed files byte-identical; preserve unregistered local files only in `.agents/skills/`. Do not add per-workflow adapter prose or create other vendor mirrors by default.
7. Treat install as first sync: `.agent-workbench.yaml` is human-owned desired config and `.agent-workbench.lock.json` is the agent-owned provenance/baseline ledger.
8. For a schema version 1 ledger, reconcile portable outputs before using `scripts/migrate_lockfile.rb`; pass the expected source repo/branch/requested ref so it can reject cross-source provenance, validate unique registered destinations and current bytes, recompute portable-workflow provenance, and write only to a new output path. Inspect the candidate before replacing the live ledger.
9. Use lockfile + current desired set to classify removal drift as confirmed upstream removal, confirmed removal with local edits, suspected legacy removal, deselected by local config, source changed / migration required, or local unmanaged. Never delete without explicit user confirmation; record kept removals in `retainedRemovals`.
10. Run `scripts/verify_skill_mirror.rb` after portable-skill copying when available; add `--claude` when the Claude target is enabled.
11. Track managed workspace files in normal repository history. Migrate the retired `workspace-config` module identifier to `repository-workspace`; do not provide a compatibility alias or create a separate configuration branch.
12. Verify with `git status --short`, `git diff --stat`, and manifest path checks when working in the workbench repository.

## Guardrails

- Do not install marketplace plugins, extensions, global/user-scope settings, or git submodules.
- Do not modify application source code during sync unless the user separately requested application changes.
- Do not create `AGENT.md`; use `AGENTS.md`.
- Do not hide managed project-wide files through `.git/info/exclude` or broad `.gitignore` rules.
- Do not delete downstream artifacts silently; deletion candidates must be normalized, allowlisted managed output paths and user-confirmed.
