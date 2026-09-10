<!-- agent-workbench: managed portable-prompt -->

# Commit Workflow Prompt

Use this vendor-neutral workflow when the user asks to prepare, create, or describe a git commit. It replaces vendor-specific commit command plugins.

## Safety Rules

- Do not commit unless the user explicitly requested a commit.
- Do not push unless the user explicitly requested a push.
- Commit exactly one logical change. Split unrelated work instead of bundling it into one commit.
- Never use `git add .` or `git add -A` unless the user explicitly asks and the full diff has been reviewed.
- Never use `--no-verify` unless explicitly authorized for this commit.
- Keep pre-commit hooks enabled. If a hook fails, diagnose and fix the underlying issue rather than bypassing it.
- Do not stage unrelated files.
- Stop and report if secrets, credentials, or unrelated destructive changes appear in the diff.

## Workflow

1. Run `git status --short`.
2. Inspect relevant diffs for all files that might be staged.
3. Confirm the staged scope is one atomic, logical change; leave unrelated edits unstaged or propose a separate commit.
4. Run project verification from `AI_AGENT_PROJECT.md` when practical.
5. Stage only intentional files.
6. Re-run `git status --short` and inspect the staged diff.
7. Write an intent-oriented Conventional Commit subject:

   ```text
   <type>[optional scope]: <why this change exists>
   ```

8. Add a concise body for non-trivial changes.
9. Add Lore trailers when they clarify decision context:

   ```text
   Constraint: <external constraint>
   Rejected: <alternative> | <reason>
   Confidence: <low|medium|high>
   Scope-risk: <narrow|moderate|broad>
   Tested: <verification>
   Not-tested: <known gap>
   ```

10. Commit without bypassing pre-commit hooks.
11. Report the commit hash, files included, verification result, hook outcome, and any push/PR step left for later.

## Commit Message Example

```text
feat(agent-workbench): make portable workflows part of every sync

Projects now receive canonical prompts and skills under `.agents/`
so Claude, Codex, Gemini, and other agents can use the same workflows
without marketplace or global setup.

Constraint: Consumer projects must stay vendor-neutral
Rejected: Vendor-specific plugins as source of truth | duplicates workflow logic
Confidence: high
Scope-risk: moderate
Tested: Manifest paths validated and diff inspected
```
