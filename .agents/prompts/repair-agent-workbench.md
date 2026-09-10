<!-- agent-workbench: managed portable-prompt -->

# Repair Agent Workbench Prompt

Repair missing or malformed agent-workbench instruction files in a consumer repository while preserving project-specific manual content.

## Allowed repairs

You may create or repair only:

- `AI_AGENT_GUIDE.md`
- `AI_AGENT_PROJECT.md` if missing
- `CLAUDE.md`
- `AGENTS.md`
- `GEMINI.md`
- `opencode.json`
- `.codex/config.toml`
- `.agent-workbench.yaml`
- `.agent-workbench.lock.json`
- `.agents/prompts/<registered-prompt>.md`
- `.agents/skills/<registered-skill>/SKILL.md`
- Registered skill resources under `.agents/skills/<registered-skill>/scripts/`, `references/`, and `assets/` when present in the workbench source
- `.claude/skills/<registered-skill>/**` when `targets.claude: true`, as an exact generated mirror of the registered portable skill directory
- exact local `.git/info/exclude` entries that hide managed project-wide paths, only to remove those stale entries when the repository uses Git
- exact `.gitignore` entries that hide managed project-wide paths, only to remove those stale entries while preserving all unrelated rules and comments

Do not modify application source code. Do not install dependencies, plugins, marketplaces, submodules, global configuration, or user-scope settings.
Do not create or refresh a separate workspace configuration branch. Do not stage, commit, push, or delete a legacy branch unless the user requested the corresponding Git action.

## Repair process

1. Inspect the repository and current instruction files.
2. Read `.agent-workbench.yaml`; if missing or unusable, recreate it from `templates/agent-workbench.yaml.tpl` using `profile: base` unless the user requested another profile. Keep it as human-owned desired configuration only. If it selects the retired `workspace-config` module, replace that identifier with `repository-workspace`; there is no compatibility alias.
3. Resolve profile and modules using `manifest.yaml` and `profiles/*.yaml`.
4. Recreate `AI_AGENT_GUIDE.md` from selected modules.
5. Preserve every existing `AI_AGENT_GUIDE.md` manual block exactly:
   - `<!-- agent-workbench:manual-begin -->`
   - `<!-- agent-workbench:manual-end -->`
6. Create `AI_AGENT_PROJECT.md` only if missing. If it exists, do not rewrite it.
7. Recreate thin `CLAUDE.md`, `AGENTS.md`, and `GEMINI.md` from templates if missing or bloated.
8. Merge `opencode.json` conservatively:
   - Preserve unrelated settings.
   - Add `AI_AGENT_GUIDE.md` and `AI_AGENT_PROJECT.md` to `instructions`.
   - Add `$schema` only if absent.
9. Merge `.codex/config.toml` conservatively:
   - Preserve unrelated settings and comments when practical.
   - Add `project_doc_max_bytes = 65536` only if absent.
10. Repair `.agent-workbench.lock.json` provenance ledger:
   - If missing in a repo that has generated workbench artifacts, run the same legacy infer-and-warn classification used by sync before rebuilding the baseline.
   - If malformed, report the parse/schema problem and ask whether to rebuild the baseline, run legacy infer-and-warn, or abort.
   - Never delete downstream artifacts while repairing the ledger unless the user explicitly confirms deletion after seeing the classified candidates.
   - Recreate the ledger only with normalized repository-relative paths inside allowed managed outputs.
   - Migrate schema version 1 ledgers only after portable outputs are reconciled. When available, use `skills/sync-agent-workbench/scripts/migrate_lockfile.rb` with the expected source repo/branch/requested ref to verify source identity, registered destinations, and exact current bytes; recompute workflow checksums and resource manifests; preserve unrelated records and retained evidence; and write a schema version 2 candidate to a new sibling temporary path. Inspect and parse the candidate before atomically replacing the live ledger. Never finalize migration from a mismatched source, stale adapter checksums, or an unmatched/duplicate legacy record.
11. Repair portable workflows:
   - Read registered `portable_prompts` and `portable_skills` directly from `manifest.yaml`.
   - Copy registered `portable_prompts` into `.agents/prompts/`.
   - Copy registered `portable_skills`, including their registered resources, into `.agents/skills/`.
   - When `targets.claude: true`, copy the registered managed source/resource set for each portable skill to `.claude/skills/<name>/`, keeping corresponding managed files byte-identical. Preserve unregistered local files in `.agents/skills/<name>/` without copying them into the generated Claude mirror. Do not append adapter prose or alter frontmatter.
   - Run `skills/sync-agent-workbench/scripts/verify_skill_mirror.rb` when available after copying; include `--claude` when that target is enabled. Treat missing, differing, or unregistered in-mirror Claude files as repair failures.
   - Preserve unregistered local prompts and skills.
   - Prefer real copied files over symlinks.
   - Do not create other vendor-specific mirrors unless the user explicitly requests them.
   - Classify stale or removed artifacts as confirmed upstream removal, confirmed removal with local edits, suspected legacy removal, deselected by local config, source changed / migration required, or local unmanaged before suggesting cleanup.
   - Preserve `retainedRemovals` when rewriting `.agent-workbench.lock.json`.
12. Repair repository-tracking hygiene:
   - Treat core agent-workbench managed files as project-wide configuration in normal branch history.
   - Remove only exact `.git/info/exclude` or `.gitignore` entries that hide those managed paths; preserve unrelated ignore rules and genuinely local files.
   - Leave created or repaired managed files visible in normal Git status. Do not stage or commit them unless the user requested that Git action.
   - If managed files exist only on a legacy `workspace-config` branch, compare and copy the intended versions into the current clean normal branch. Preserve newer project-owned content and do not merge unrelated histories wholesale.
   - Never create, refresh, or use the legacy branch as the active source. Report local or remote legacy branches as cleanup remaining after `main` is verified; deletion requires explicit authorization.

## Malformed config handling

If JSON or TOML is malformed:

- Report the parse error.
- In repair mode, preserve the original content in a clearly named local backup next to the file, such as `opencode.json.agent-workbench-backup`.
- Write the minimal valid repaired config. For `.agent-workbench.lock.json`, rebuild the provenance ledger only after the user chooses the safe migration path; otherwise leave it unchanged or back it up as reported.
- Do not discard unrelated settings unless they cannot be parsed; mention that limitation in the final report.

## Final report

Summarize:

- Files repaired or created.
- Files intentionally left untouched.
- Manual content preserved.
- Portable prompts and skills repaired.
- Backups created.
- Any assumptions, retained removals, malformed lockfile issues, or unresolved removal classifications.
- Managed-path Git tracking, forced module migration, stale ignore cleanup, any remaining legacy branch, and `.agent-workbench.lock.json` repair status.
- Confirmation that no application source code or global configuration was changed.
