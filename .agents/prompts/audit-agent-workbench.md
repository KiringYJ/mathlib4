<!-- agent-workbench: managed portable-prompt -->

# Audit Agent Workbench Prompt

Audit a consumer repository for consistency with the vendor-neutral `agent-workbench` model. This prompt is read-only unless the user explicitly asks for repairs.

## Read-only rule

Do not modify files in audit mode. Inspect and report only.

## Checks

1. `AI_AGENT_GUIDE.md`
   - Exists.
   - Contains the managed metadata marker with `agent-workbench: managed`.
   - References the selected profile and source.
   - Does not contain obvious unmarked project-specific content that should live in `AI_AGENT_PROJECT.md`.

2. `AI_AGENT_PROJECT.md`
   - Exists, or the repository clearly documents that it is intentionally absent.
   - Contains project-specific sections for architecture, build commands, test commands, important files, domain terms, and constraints when possible.

3. `CLAUDE.md`
   - Is a thin entrypoint.
   - References `@AI_AGENT_GUIDE.md` and `@AI_AGENT_PROJECT.md`.
   - Does not contain a large duplicated copy of the shared guide.

4. `AGENTS.md`
   - Is a thin Codex/OpenCode/general entrypoint.
   - Tells agents to read `AI_AGENT_GUIDE.md` and `AI_AGENT_PROJECT.md`.
   - Does not rely on `@` imports.
   - Does not contain a large duplicated copy of the shared guide.

5. `GEMINI.md`
   - Is a thin entrypoint.
   - References `@AI_AGENT_GUIDE.md` and `@AI_AGENT_PROJECT.md`.
   - Does not contain a large duplicated copy of the shared guide.

6. `opencode.json`
   - Is valid JSON.
   - Includes `AI_AGENT_GUIDE.md` and `AI_AGENT_PROJECT.md` in `instructions`.
   - Preserves unrelated settings.

7. `.codex/config.toml`
   - Exists when Codex config is enabled in `.agent-workbench.yaml`.
   - Is project-scoped.
   - Does not depend on user-scope or machine-local paths.

8. `.agent-workbench.yaml`
   - Exists.
   - Has valid `source`, `profile`, `modules`, `targets`, and `preserve` sections.
   - Names modules that exist in the workbench manifest.
   - Is treated as desired configuration only, not noisy sync state.

9. `.agent-workbench.lock.json` provenance ledger
   - Exists after a full sync or first install unless the repository is intentionally legacy/no-lockfile.
   - Is valid schema version 2 JSON with `source.resolvedCommit`, `manifestDigest`, `syncMode`, `targets`, scoped baselines, `installedArtifacts`, and `retainedRemovals` when present.
   - Reports schema version 1 `vendor_adapters`, `capability`, or `vendor` fields as a known migration requirement rather than an upstream removal.
   - Records only normalized repository-relative output paths inside allowed managed output paths.
   - Does not contain absolute paths, `..` traversal, or application source paths as managed deletion candidates.
   - Separates human config (`.agent-workbench.yaml`) from agent-owned baseline/provenance state.
   - Reports retained removals and malformed/stale lockfile state without modifying files.

10. Portable workflows
   - `manifest.yaml` registers portable prompts and skills directly, and every registered source exists.
   - `.agents/prompts/` contains the registered portable prompts from the workbench manifest.
   - `.agents/skills/` contains the registered portable skills from the workbench manifest.
   - Canonical workflow content lives under `.agents/`, not only in Claude/Codex/Gemini/OpenCode-specific folders.
   - If the Claude target is enabled, every registered managed file in `.claude/skills/<name>/` is byte-identical to the corresponding `.agents/skills/<name>/` file. Unregistered local files under `.agents/skills/<name>/` are outside mirror parity and remain preserved only in the canonical tree.
   - No per-workflow capability registry or generic vendor adapter note is required for standard skill distribution.
   - No registered portable prompt or skill is a symlink.

11. Removal and drift classification
   - Reports **confirmed upstream removal** only when a usable lockfile record and current desired set prove the artifact is no longer selected upstream.
   - Reports **confirmed removal with local edits** when a removed artifact's local checksum differs from the last applied output.
   - Reports **suspected legacy removal** only for no-lockfile repos with objective managed ownership signals.
   - Reports **deselected by local config** when current profile or targets stop selecting a previously generated artifact.
   - Reports **source changed / migration required** when repo, branch, manifest, source path, or artifact id prevents safe comparison after applying any known lockfile schema migration.
   - Reports **local unmanaged** for artifacts without a lockfile record or objective managed ownership signal, and does not frame them as upstream removals.
   - Confirms that audit mode never deletes files and only suggests safe repair/sync actions.

12. Vendor neutrality
   - No Claude marketplace/plugin dependency is required for guide loading.
   - No git submodule is required.
   - No global or user-scope configuration is required.
   - No `AGENT.md` typo exists as the primary entrypoint.

13. Repository-tracked workspace policy
   - The resolved module set includes `repository-workspace` and does not include the retired `workspace-config` identifier. Treat the legacy identifier as a migration failure, not a supported alias.
   - Core agent-workbench managed files, including `.agent-workbench.lock.json`, are tracked in ordinary repository history or are visible as pending additions from the current sync.
   - `main` is the authoritative source for shared agent/editor configuration; normal clones do not depend on an auxiliary branch or restore step.
   - `.git/info/exclude` and `.gitignore` do not hide managed project-wide paths. Personal, machine-local, generated, cached, or secret-bearing files may remain ignored.
   - If a legacy `workspace-config` branch exists, report whether it contains content missing from `main`. Missing content is a migration failure; a fully superseded branch is cleanup debt and must not be deleted in audit mode.

## Output

Return a structured report:

- Overall status: `PASS`, `WARN`, or `FAIL`.
- Findings grouped by severity.
- Exact files and lines when practical.
- Suggested repair action for each issue.
- Confirmation that no files were modified.
- Lockfile status, retained removals, and any confirmed upstream removal, confirmed removal with local edits, suspected legacy removal, deselected by local config, source changed / migration required, or local unmanaged findings.
