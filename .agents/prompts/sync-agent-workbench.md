<!-- agent-workbench: managed portable-prompt -->

# Sync Agent Workbench Prompt

Use this LLM-executed workflow to synchronize a consumer repository with the vendor-neutral `agent-workbench` model.

## Outcome and completion contract

Reconcile the requested workbench scopes with the resolved source, profile, manifest, and templates while preserving project-owned content and keeping application code outside the sync.

A sync is complete when:

- the selected profile and every selected module resolve to registered, existing files;
- the active scopes match the resolved workbench source;
- `AI_AGENT_PROJECT.md`, marked manual blocks, unrelated config, and unregistered local workflows are preserved;
- the provenance ledger advances only for scopes that completed successfully;
- relevant parse, path-safety, idempotence, and Git diff checks pass; and
- the final report identifies changed, preserved, skipped, and blocked items.

Reading files, generating or updating allowed local artifacts, removing exact stale ignore entries that hide managed files, and running non-destructive validation are authorized by a sync request. Ask only when deletion, destructive Git work, source migration, malformed-state recovery, unrequested staging/commit/publication, or a material expansion of scope requires a user decision. Stop after the completion criteria are met.

## Supported natural-language modes

Interpret the user's request and select one mode:

- **full sync**: update managed guide, thin entrypoints, OpenCode config, Codex config, portable prompts, portable skills, create missing project/config files, and update the `.agent-workbench.lock.json` provenance ledger for the scopes actually reconciled.
- **guide-only sync**: update only `AI_AGENT_GUIDE.md` and create `.agent-workbench.yaml` if missing.
- **entrypoints-only sync**: update only `CLAUDE.md`, `AGENTS.md`, `GEMINI.md`, `opencode.json`, and `.codex/config.toml`.
- **portable-workflows sync**: update only managed `.agents/prompts/`, `.agents/skills/`, and selected `.claude/skills/` discovery-mirror artifacts.
- **audit-only mode**: inspect and report; do not modify files.
- **repair missing files**: create or repair missing/malformed instruction/config files while preserving manual content.

If the user does not specify a mode, use **full sync**. If the user asks to install agent-workbench, treat install as the first sync: run the same workflow, create missing config/artifacts, and write the first provenance ledger. If the user specifies a profile (for example `rust`, `python`, `typescript`, `frontend`, `vue`, `vue-vuetify`, `research`, or `tex`), set that profile in `.agent-workbench.yaml` and include its inherited modules.

## Hard safety rules

- Do not modify application source code.
- Do not install dependencies.
- Do not install Claude plugins, Claude marketplace entries, global Codex settings, global Gemini settings, or user-scope configuration.
- Do not create git submodules.
- Do not rely on machine-local absolute paths.
- Do not create `AGENT.md`; the correct file is `AGENTS.md`.
- Do not create or refresh a separate workspace configuration branch; managed project-wide files belong in normal repository history.
- Do not hide managed project-wide files through `.git/info/exclude` or broad `.gitignore` rules.
- Do not stage, commit, push, or delete a legacy branch unless the user requested the corresponding Git action.
- Only update these files unless the user explicitly authorizes more:
  - `AI_AGENT_GUIDE.md`
  - `AI_AGENT_PROJECT.md` only when missing
  - `CLAUDE.md`
  - `AGENTS.md`
  - `GEMINI.md`
  - `opencode.json`
  - `.codex/config.toml`
  - `.agent-workbench.yaml`
  - `.agent-workbench.lock.json`
  - `.agents/prompts/<registered-prompt>.md`
  - `.agents/skills/<registered-skill>/SKILL.md`
  - `.agents/skills/<registered-skill>/scripts/**`, `.agents/skills/<registered-skill>/references/**`, and `.agents/skills/<registered-skill>/assets/**` when present in the workbench source
  - `.claude/skills/<registered-skill>/**` when `targets.claude: true`, as an exact generated mirror of the registered portable skill directory
  - exact local `.git/info/exclude` entries that hide managed paths listed in this prompt, only to remove those stale entries when the repository uses Git
  - exact `.gitignore` entries that hide managed paths listed in this prompt, only to remove those stale entries while preserving all unrelated rules and comments

## Repository-tracked workspace policy

Agent-workbench managed files are project-wide workspace configuration by default. In Git repositories, track them in ordinary branch history so contributors receive them with a normal clone and `main` remains the single source of truth.

Required invariant:

```text
shared agent and editor configuration is visible to normal Git status and versioned with the project.
```

Before writing files in a consumer Git repository:

1. Detect the current branch and existing tracked files with `git status --short`, `git branch --show-current`, and `git ls-files -- <workspace-paths>`.
2. Treat the core managed paths below as project-wide files in the current normal development branch. Only optional editor or automation paths may be classified as personal or machine-local in `AI_AGENT_PROJECT.md`.
3. Inspect `.git/info/exclude` and `.gitignore`. Remove only exact stale entries that hide managed project-wide paths; preserve unrelated ignore rules and genuinely local files.
4. If files exist only on a legacy `workspace-config` branch, compare and copy the intended paths into the current clean normal branch. Do not merge unrelated branch histories wholesale, overwrite newer project-owned content, or delete the legacy branch without explicit authorization.
5. Generate or refresh the workspace files in the working tree and leave them visible in normal Git status. Do not stage or commit them unless the user requested that Git action.
6. Do not create or update a separate workspace configuration branch. Push only when the user explicitly requested remote publication or already asked for publish/push.

Default agent-workbench managed project paths:

```text
AI_AGENT_GUIDE.md
AI_AGENT_PROJECT.md
AGENTS.md
CLAUDE.md
GEMINI.md
.agent-workbench.yaml
.agent-workbench.lock.json
.agents/
.codex/
.claude/
opencode.json
```

Optional workspace paths such as `.agent/`, `.cursor/`, `.vscode/`, `prompts/`, or `scripts/` may also be tracked when they are useful to every contributor. Classify them before writing: shared deterministic configuration belongs in the repository, while personal settings, secrets, caches, absolute machine paths, and local runtime state stay untracked.

### Forced migration from the retired branch layout

The `workspace-config` module identifier and orphan-branch layout are retired. There is no compatibility alias.

- In full sync, guide-only sync, or repair mode, replace a selected `workspace-config` module with `repository-workspace` in `.agent-workbench.yaml` before resolving modules. Do not keep both identifiers.
- In audit-only mode, report the legacy module identifier as a failure that requires migration.
- If managed files exist only on a legacy `workspace-config` branch, copy the intended versions into the current clean normal branch, preserve newer project-owned content, and expose the results to normal Git status.
- Remove only exact legacy `.git/info/exclude` or `.gitignore` entries that hide managed project-wide paths. Preserve unrelated ignore rules and comments.
- Update the provenance ledger for successfully reconciled scopes using the new manifest/module identity. Do not preserve an alias or keep the old branch as an active source.
- Do not delete local or remote legacy branches automatically. Report them as cleanup remaining after `main` contains and verifies all intended files; branch deletion requires an explicit request.

## Inputs to read

1. Inspect the consumer repository root.
2. Read `.agent-workbench.yaml` if present. Treat it as human-owned desired configuration only.
3. Read `.agent-workbench.lock.json` if present. Treat it as an agent-owned provenance/baseline ledger, not as user configuration or a package-manager lock.
4. Read existing managed files if present, especially `AI_AGENT_GUIDE.md`, to preserve manual blocks.
5. If the repository uses Git, inspect the current branch, local `.git/info/exclude`, `.gitignore`, whether managed paths are tracked on the current branch, and whether a legacy `workspace-config` branch contains content that still needs migration.
6. Read the workbench source files from the current checkout or from `KiringYJ/agent-workbench` if the user references the repository remotely:
   - `manifest.yaml`
   - selected `profiles/*.yaml`
   - selected `guide/**/*.md`
   - `templates/*.tpl`
   - registered `portable_prompts` and `portable_skills` from `manifest.yaml`

## Provenance ledger and removal detection

`.agent-workbench.yaml` is the human-owned desired configuration. Do not store generated sync state there.

`.agent-workbench.lock.json` is an agent-owned provenance/baseline ledger. It records what the last successful sync actually installed for each scope so later syncs can detect removed, deselected, locally edited, or migrated artifacts. It is shared project configuration and should be tracked in normal repository history with the managed files it describes.

Minimum lockfile shape:

```json
{
  "schemaVersion": 2,
  "generatedAt": "<iso-8601>",
  "source": {
    "repo": "KiringYJ/agent-workbench",
    "branch": "main",
    "requestedRef": "main",
    "resolvedCommit": "<upstream-sha>"
  },
  "manifestDigest": "sha256:<digest>",
  "profile": "base",
  "syncMode": "full|guide-only|entrypoints-only|portable-workflows|repair",
  "targets": { "guide": true, "portable_prompts": true, "portable_skills": true },
  "scopes": {
    "guide": { "resolvedCommit": "<sha>", "manifestDigest": "sha256:<digest>", "lastReconciledAt": "<iso-8601>" },
    "entrypoints": { "resolvedCommit": "<sha>", "manifestDigest": "sha256:<digest>", "lastReconciledAt": "<iso-8601>" },
    "portable_prompts": { "resolvedCommit": "<sha>", "manifestDigest": "sha256:<digest>", "lastReconciledAt": "<iso-8601>" },
    "portable_skills": { "resolvedCommit": "<sha>", "manifestDigest": "sha256:<digest>", "lastReconciledAt": "<iso-8601>" }
  },
  "installedArtifacts": [
    {
      "id": "portable_skill:sync-agent-workbench",
      "kind": "portable_skill",
      "scope": "portable_skills",
      "name": "sync-agent-workbench",
      "sourcePath": "skills/sync-agent-workbench/SKILL.md",
      "outputPath": ".agents/skills/sync-agent-workbench/SKILL.md",
      "sourceChecksum": "sha256:<source>",
      "lastAppliedOutputChecksum": "sha256:<output>",
      "resourceManifest": [
        {
          "path": "scripts/migrate_lockfile.rb",
          "sourceChecksum": "sha256:<resource-source>",
          "lastAppliedOutputChecksum": "sha256:<resource-output>"
        },
        {
          "path": "scripts/verify_skill_mirror.rb",
          "sourceChecksum": "sha256:<resource-source>",
          "lastAppliedOutputChecksum": "sha256:<resource-output>"
        }
      ],
      "markerVersion": "agent-workbench: managed portable-skill",
      "profile": "base",
      "managed": true
    }
  ],
  "retainedRemovals": []
}
```

Artifact records should include all generated files in a skill folder (`scripts/`, `references/`, `assets/`) through `resourceManifest`. Record a Claude discovery mirror as another `portable_skills` artifact with the same `sourcePath` and a `.claude/skills/<name>/...` output path. `manifestDigest` should cover the resolved manifest and selected profile enough to explain why the desired artifact set changed.

### Legacy capability metadata migration

Schema version 1 ledgers may contain a `vendor_adapters` scope and per-artifact `capability` or `vendor` fields from the retired capability registry. Treat those fields as known legacy metadata, not as evidence that the underlying workflow was removed or that the source changed.

During a full sync, portable-workflows sync, or lockfile repair:

1. Match legacy records to current registered prompts and skills by normalized `sourcePath` and `outputPath`.
2. Preserve unrelated artifact records, pre-migration timestamps, local-edit evidence, and `retainedRemovals`. Portable-workflow checksums and resource manifests are replaced only with verified current provenance in step 5.
3. Move managed Claude skill records into the `portable_skills` scope and use the canonical skill path as their source.
4. Reconcile the registered prompt and skill files first. Then, when available, run `skills/sync-agent-workbench/scripts/migrate_lockfile.rb` with the resolved workbench manifest, consumer root, expected source repo/branch/requested ref, real manifest digest, resolved commit, and reconciliation timestamp. The expected source identity must match the v1 ledger; otherwise stop with source changed / migration required. Write to a new sibling temporary path, never over the live ledger.
5. The migration must verify current source/output bytes, reject destinations outside the exact registered portable-workflow paths, recompute workflow checksums and resource manifests, and preserve unrelated artifact records and retained evidence. A stale generated adapter is not valid v2 provenance.
6. Drop the obsolete `vendor_adapters` scope and `capability`/`vendor` fields only after the affected portable workflow scope reconciles successfully.
7. Inspect and parse the candidate, finish any other active-scope updates, and only then atomically replace the live ledger with schema version 2. Do not delete an unmatched or duplicate legacy artifact; classify it with the normal removal rules and request any required decision.

### Active scopes and baseline advancement

Advance only the scopes actually reconciled by the selected mode:

- full sync: all selected scopes.
- guide-only sync: `guide` only.
- entrypoints-only sync: `entrypoints` and vendor config only.
- portable-workflows sync: `portable_prompts` and `portable_skills`, including the Claude discovery mirror when selected.
- repair missing files: only repaired scopes and artifacts.

Do not classify or delete artifacts from inactive scopes. Do not advance inactive scope baselines.

### Generated artifact deletion scope

Deletion candidates must normalize to repository-relative paths and stay inside the allowed managed outputs:

- `AI_AGENT_GUIDE.md`
- `CLAUDE.md`
- `AGENTS.md`
- `GEMINI.md`
- `opencode.json`
- `.codex/config.toml`
- `.agents/prompts/<registered-prompt>.md`
- `.agents/skills/<registered-skill>/**`
- `.claude/skills/<registered-skill>/**` when generated by the Claude target
- explicitly requested and lockfile-recorded vendor mirrors such as `.codex/skills/**`, `.gemini/skills/**`, or `.opencode/skills/**`

Never delete absolute paths, paths outside the repository root, paths containing `..` traversal, malformed paths, application source files, or local/unmanaged artifacts. `.agent-workbench.lock.json` may be repaired or recreated, but normal upstream-removal cleanup should not delete the ledger itself.

### Removal and drift classification

Use lockfile records plus the current resolved desired set as primary evidence. Use upstream Git history/diff as supporting explanation, not as the only basis for deletion. Use objective ownership signals: lockfile record, managed marker, checksum match against known source/output, tombstone/migration metadata, or explicit user confirmation.

Classify every candidate with one of these exact statuses:

1. **confirmed upstream removal** — lockfile recorded a managed artifact, source identity still matches, current desired set omits it, and local checksum matches the last applied output or the local output is already gone.
2. **confirmed removal with local edits** — same as confirmed upstream removal, but local checksum or resource manifest differs from the lockfile. Default to keep/backup; do not include it in a broad safe delete-all choice unless explicitly selected.
3. **suspected legacy removal** — no usable lockfile exists, but an objective managed ownership signal exists and the artifact is absent from the current upstream manifest. Say this is inferred, not confirmed by Git history.
4. **deselected by local config** — the artifact exists or is lockfile-recorded, but the current profile/targets/sync mode no longer selects it. Do not call this an upstream removal.
5. **source changed / migration required** — source repo, branch, manifest digest, artifact id, or source path changed enough that comparison is unsafe. Stop removal classification for affected artifacts and ask for a migration/audit decision. Do not use the retired capability metadata alone as this evidence; apply the schema version 1 migration above first.
6. **local unmanaged** — no lockfile record and no objective managed ownership signal. Preserve by default and do not present as an upstream-removal candidate.

If the upstream manifest provides tombstone, rename, `renamed_from`, `supersedes`, or removed-artifact metadata, use it to produce migration prompts instead of treating the change as a simple delete plus new install.

### User confirmation for deletion

Never delete a downstream artifact without explicit user confirmation. Group candidates by status and ask with choices equivalent to:

- Keep all.
- Delete all safe candidates.
- Delete selected candidates.
- Skip/abort deletion for this sync.

Local-edited, migration-required, unsafe-path, and malformed-lockfile candidates are not safe candidates. If the current environment cannot ask interactively, report candidates and skip deletion.

If the user keeps a confirmed or suspected removal, record it in `retainedRemovals` with artifact id, output path, status at retention time, timestamp, and reason such as `user chose keep`. Preserve retained-removal context on later syncs so the agent does not lose evidence or repeatedly ask the same ambiguous question without context.

### Lockfile atomicity and malformed state

Validate the lockfile before using it. If JSON is malformed, required fields are missing, paths are unsafe, or source identity changed, report the issue and ask whether to rebuild the baseline, run legacy infer-and-warn, or abort. Do not delete artifacts from a malformed ledger.

Rewrite `.agent-workbench.lock.json` only after all selected writes/deletes complete successfully. If sync partially fails, leave the previous ledger intact or write a clearly reported pending/repair note only with user approval.

## Profile and module resolution

1. If `.agent-workbench.yaml` is missing, create it from `templates/agent-workbench.yaml.tpl` with `profile: base`, unless the user requested another profile.
2. If `.agent-workbench.yaml` selects the retired `workspace-config` module, replace it with `repository-workspace` as the required breaking migration. Do not accept or synthesize an alias.
3. Load `manifest.yaml`.
4. Resolve the selected profile from `profiles/<profile>.yaml`.
5. If a profile has `extends`, load the parent profile first.
6. Concatenate modules in this order:
   - parent profile modules
   - child profile modules
   - explicit `modules:` listed in `.agent-workbench.yaml` that are not already included
7. Validate each module name exists in `manifest.yaml`.
8. If a requested module is missing, report it and continue only if enough modules remain to produce a useful guide. The retired `workspace-config` identifier is handled only by the forced migration above, never as a compatibility module.

## AI_AGENT_GUIDE.md generation

Generate `AI_AGENT_GUIDE.md` from `templates/AI_AGENT_GUIDE.md.tpl`.

The top metadata marker must be:

```html
<!--
agent-workbench: managed
source: <repo-or-url>
profile: <profile-name>
manual-edits: preserve-marked-sections-only
-->
```

Rules:

- Compose the body from the selected guide modules.
- Preserve existing content inside every manual block exactly:
  - `<!-- agent-workbench:manual-begin -->`
  - `<!-- agent-workbench:manual-end -->`
- Put preserved manual blocks near the top under a `## Preserved Manual Notes` heading, or leave them where the template indicates manual blocks.
- Do not preserve unmarked manual edits in `AI_AGENT_GUIDE.md`; tell the user that only marked blocks are retained.
- The result must be idempotent: running sync again with the same inputs should produce the same file.

## AI_AGENT_PROJECT.md

- If `AI_AGENT_PROJECT.md` is missing, create it from `templates/AI_AGENT_PROJECT.md.tpl`.
- If it already exists, never overwrite or rewrite it.
- This file is the correct place for architecture, build commands, test commands, important paths, domain terms, and project-specific constraints.

## Thin entrypoints

Create or update these files from templates:

- `CLAUDE.md`: thin Claude Code entrypoint using `@AI_AGENT_GUIDE.md` and `@AI_AGENT_PROJECT.md`.
- `AGENTS.md`: thin Codex/OpenCode/general entrypoint. Do not use `@` imports here.
- `GEMINI.md`: thin Gemini entrypoint using `@AI_AGENT_GUIDE.md` and `@AI_AGENT_PROJECT.md`.

Vendor-specific files must not contain a large duplicated copy of the guide.

## OpenCode config merge

Ensure `opencode.json` includes:

```json
{
  "$schema": "https://opencode.ai/config.json",
  "instructions": [
    "AI_AGENT_GUIDE.md",
    "AI_AGENT_PROJECT.md"
  ]
}
```

If `opencode.json` exists:

- Parse it as JSON.
- Preserve unrelated settings.
- Preserve existing instruction entries.
- Add `AI_AGENT_GUIDE.md` and `AI_AGENT_PROJECT.md` if missing.
- Add `$schema` only if absent.
- Keep output formatted with two-space indentation.

If it is malformed, do not discard it silently. Report the parse error and either repair only with user permission or write a clear backup if the user requested repair mode.

## Codex config merge

Ensure `.codex/config.toml` exists with:

```toml
#:schema https://developers.openai.com/codex/config-schema.json

project_doc_max_bytes = 65536
```

If `.codex/config.toml` exists:

- Preserve unrelated settings and comments when practical.
- Add `project_doc_max_bytes = 65536` only if no `project_doc_max_bytes` setting exists.
- Do not overwrite project-specific model, approval, sandbox, tool, or path settings.

## Portable prompts and skills

For full sync and portable-workflows sync, copy the registered workflow artifacts from the workbench manifest into project-local vendor-neutral paths:

- `portable_prompts.<name>.path` -> `.agents/prompts/<name>.md`
- `portable_skills.<name>.path` -> `.agents/skills/<name>/SKILL.md`
- when `targets.claude: true`, `portable_skills.<name>.path` -> `.claude/skills/<name>/SKILL.md` with the rest of the registered skill directory mirrored alongside it

Rules:

- Create `.agents/prompts/` and `.agents/skills/` when missing.
- Copy the managed prompt/skill content from the workbench source.
- If a registered skill folder contains `scripts/`, `references/`, or `assets/`, copy those resources into `.agents/skills/<name>/`.
- Do not delete unregistered local prompts or skills.
- Do not overwrite files under `.agents/skills/<name>/` that are not part of the registered managed source skill.
- Prefer real copied directories over symlinks for portability.
- Do not create vendor-specific mirrors such as `.codex/skills/`, `.gemini/skills/`, or `.opencode/skills/` unless the user explicitly requests them.
- When `targets.claude: true`, copy every registered managed file in each portable skill directory to `.claude/skills/<name>/` so Claude Code can discover it. For the registered managed source/resource set, the Claude files must be byte-identical to the corresponding `.agents/skills/<name>/` files: do not append adapter prose, change frontmatter, or omit registered resources. Preserve unregistered local files under `.agents/skills/<name>/`, but do not copy them into the generated Claude mirror. Do not install Claude plugins or marketplace entries.
- After copying, run `skills/sync-agent-workbench/scripts/verify_skill_mirror.rb <workbench-root> <consumer-root> --claude` when the helper is available and the Claude target is enabled. Without Claude, omit `--claude`. Treat any missing or differing registered file, or any unregistered file inside a registered Claude mirror directory, as a failed sync.
- For Codex, Gemini, and OpenCode, prefer `.agents/skills/<name>/SKILL.md` as the shared generated surface unless the user explicitly requests a vendor-native mirror.
- If the active vendor exposes a compatible built-in or installed implementation, it may be the preferred invocation when available, but still keep the neutral fallback skill available. Record this policy in the canonical skill or prompt instead of a per-vendor adapter file.
- Treat `agent-workbench: managed portable-prompt` and `agent-workbench: managed portable-skill` as overwrite markers.
- If a consumer project already has a local `.agents/prompts/<name>.md` or `.agents/skills/<name>/SKILL.md` with unmarked manual edits, replace it only when the file carries an agent-workbench managed marker or when the user requested repair/full overwrite. Otherwise report the conflict.
- Before copying portable workflows, compare the current desired set with `.agent-workbench.lock.json` for the active scopes. Present confirmed upstream removal, confirmed removal with local edits, suspected legacy removal, deselected by local config, source changed / migration required, and local unmanaged findings using the classification rules above.
- After copying and after any user-confirmed deletion choices, update `.agent-workbench.lock.json` for only the active scopes and preserve `retainedRemovals`.

## Final report

End with a concise diff-style summary:

- Mode and profile used.
- Completion evidence: manifest/profile path validation, config parse results, idempotence or repeat-run status, and Git diff/status checks.
- Files created.
- Files updated.
- Files intentionally left unchanged, especially `AI_AGENT_PROJECT.md`.
- Manual blocks preserved.
- Portable prompts and skills synced or skipped.
- Any parse errors, skipped modules, malformed lockfile issues, retained removals, or assumptions.
- Git tracking status for managed paths, exact stale ignore entries removed, any legacy-branch migration findings, and whether `.agent-workbench.lock.json` was created or updated.
- Confirmation that no application source code, dependencies, global config, marketplace, plugin installation, or submodule was modified.
