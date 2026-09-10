# Project-Specific Agent Context

## Purpose

This fork is a personal working distribution of mathlib. It keeps the upstream
implementation and contribution workflow available while providing a place to
develop and retain improvements that make formalized mathematics more natural
for mathematicians.

The policies below are project-local overrides. In particular, generic
agent-workbench references to `main` as the workspace source of truth do not
apply: this fork has no `main` branch.

## Branch Model

- `master` is a protected mirror of `leanprover-community/mathlib4:master`.
  It must contain no personal commits, workbench files, or other fork-only
  changes. Update local `master` only by fetching `upstream` and fast-forwarding
  it to `upstream/master`.
- `dev` is the canonical personal branch and daily driver. It contains the
  complete preferred working version: current upstream plus pending, rejected,
  experimental, and not-yet-submitted improvements. The agent-workbench files
  are tracked only on this personal line of development.
- `pr/<slug>` branches are short-lived, clean exports for upstream review.
  Create them from a freshly fast-forwarded `master`; never merge `dev`
  wholesale into them.
- `exp/<slug>` may be used for work whose mathematical or API direction is not
  yet settled.

After an explicitly authorized publication, `origin/master` should point to
the same commit as `upstream/master`. Do not infer authorization to push from a
fetch, sync, or local branch update. All pushes go to `origin`; never push to
`upstream`.

Keep logically independent changes in separate, semantically coherent commits
on `dev`. This makes upstream exports and long-term rebases auditable even when
the personal branch has accumulated many changes.

## Upstream Export Workflow

1. Finish and verify the coherent change on `dev`.
2. Fetch `upstream`, switch to `master`, and run
   `git merge --ff-only upstream/master`.
3. Verify that `master` and `upstream/master` resolve to the same commit.
4. Create `pr/<slug>` from `master` and cherry-pick only the contribution
   commits. Do not merge `dev` into the export branch.
5. Inspect `git diff master...HEAD`. The export must not contain workbench
   paths such as `AI_AGENT_GUIDE.md`, `AI_AGENT_PROJECT.md`, `AGENTS.md`,
   `CLAUDE.md`, `GEMINI.md`, `.agent-workbench.*`, `.agents/`, `.claude/`,
   `.codex/`, or `opencode.json`.
6. Run the relevant mathlib build, tests, linters, and documentation checks.
   Push the branch to `origin` only when publication is explicitly requested.

Clean export branches intentionally do not contain the personal workbench
files. Start substantive work on `dev`. When an agent must inspect or validate
an export branch in the same checkout, load this policy from `dev` first; in a
fresh export worktree, use `git show dev:AI_AGENT_PROJECT.md` and
`git show dev:AI_AGENT_GUIDE.md` before making changes.

An API improvement and the mathematical result that motivates it may form one
upstream contribution when they are a coherent, reviewable unit. If that unit
is too large, use stacked PRs while keeping the downstream application visible
as justification for the API. Do not rewrite an application into a less
natural API merely to manufacture independence when the API improvement is
part of the contribution. Conversely, do not include unrelated personal API
changes in an upstream export.

Upstream contribution is the default intention, not a dependency of personal
work. Address substantive mathematical, type-theoretic, compatibility,
performance, and maintenance review. If a change is delayed or rejected, keep
its commits isolated and rebasable on `dev`; upstream acceptance must not block
the formalization that motivated it.

## Mathematician-Facing Design Commitments

The public mathematical API should primarily serve mathematicians and
downstream formalizers. Implementation generality and reuse matter, but the
surface language should preserve the concepts and proof decomposition used in
mathematical practice whenever Lean permits it.

Equivalent formal expressibility is not sufficient evidence of API
equivalence. Evaluate an interface by whether:

- its statements and operations faithfully represent the mathematical object;
- a mathematician can discover declarations from standard concepts and
  terminology;
- notation matches canonical mathematical operations where that distinction
  carries meaning;
- common constructions compose without exposing representation details; and
- proof code communicates the mathematical reason a step works rather than a
  library-specific decomposition that happens to be equivalent.

For set-system objects such as sigma-algebras and Dynkin systems, membership,
inclusion, ordinary unions, generated structures, and classical named proof
principles should be available in forms that preserve their mathematical
distinctions. A generic internal theorem may remain canonical internally while
a thin mathematician-facing facade supplies the natural conceptual entry
point.

Develop API improvements against real formalizations. A motivating theorem,
paper, or repeated proof pattern is evidence about the right abstraction and
should be retained when deciding API and PR boundaries. Prefer a useful
concrete interface that has survived real use over premature generalization.
Generalize after downstream cases demonstrate the reusable structure.

Preserve strong upstream substrate when it is mathematically and technically
sound. This fork is not different for the sake of being different; it changes
interfaces where actual formalization exposes semantic or ergonomic friction.

## Working API Heuristics

These are review questions, not unconditional rules. Establish them against
concrete use cases before redesigning existing code.

- Is there a clear normal form for statements and theorem search?
- Does a coercion or typeclass hide a mathematical choice that users routinely
  need to vary explicitly?
- If an operation is totalized outside its mathematical hypotheses, is the
  fallback mathematically meaningful, clearly documented, and useful enough to
  justify the semantic cost? Would explicit evidence or a separate internal
  helper be clearer?
- Can a thin facade improve semantic fidelity without duplicating a parallel
  theorem ecosystem?
- If a better public interface replaces an established one, can a deliberate
  migration and deprecation path avoid permanent duplicate APIs?
- Does generated proof glue merely conceal an ontology mismatch? Automation
  and language models can assist discovery, but should not be used as evidence
  that a human-facing interface is already adequate.

Treat these as hypotheses to test through downstream code, not as blanket
claims about every mathlib module or maintainer. Keep criticism technical and
specific; do not put personal attacks in repository history, commits, issues,
or pull requests.

## Architecture

- `Mathlib/` contains library modules.
- `Mathlib.lean` is the generated import root and must be refreshed when new
  modules are added.
- `MathlibTest/`, `Archive/`, `Counterexamples/`, and `scripts/` provide tests,
  historical material, examples, and repository tooling.
- `AI_AGENT_GUIDE.md` is generated shared agent policy.
- `AI_AGENT_PROJECT.md` is the manually maintained policy for this fork and
  must be preserved verbatim by future workbench syncs.

## Build Commands

```powershell
lake exe cache get
lake build Mathlib.Import.Path
lake build
```

Use the narrow module build during iteration. A full build is proportional to
the scope and risk of the change; do not report it unless it actually ran.

## Test Commands

```powershell
lake test
lake exe mk_all
```

Run `lake exe mk_all` when adding a new module. Follow the live upstream mathlib
contribution guide for any additional linter or documentation checks required
for the affected area.

## Important Files and Directories

- `README.md`: upstream setup, build, and contribution entry points.
- `.github/CONTRIBUTING.md`: link to the current upstream contribution guide.
- `lakefile.lean` and `lean-toolchain`: project and Lean toolchain definitions.
- `.agent-workbench.yaml`: human-owned desired workbench configuration.
- `.agent-workbench.lock.json`: generated sync provenance and checksum ledger.

## Domain Terms

- **upstream**: `leanprover-community/mathlib4`.
- **origin**: the personal fork `KiringYJ/mathlib4`.
- **daily driver**: `dev`, the complete preferred working version.
- **clean export**: a `pr/<slug>` branch based on `master` and containing only
  the coherent contribution intended for upstream.
- **mathematician-facing facade**: a thin public interface that exposes a
  mathematical concept naturally while reusing a sound generic core.

## Workspace Configuration

All agent-workbench managed paths are shared configuration for the personal
`dev` branch and should be tracked there. Do not hide them through
`.git/info/exclude` or `.gitignore`. Do not copy, merge, or cherry-pick them into
`master` or an upstream export branch.

Personal settings, credentials, caches, absolute machine paths, and runtime
state remain untracked. Future full syncs may update generated managed files
and the provenance ledger, but must never rewrite this project file.

## Project-Specific Constraints

- Inspect the current branch before editing. Never make personal changes on
  `master`.
- Keep upstream hooks enabled and follow mathlib naming, style, documentation,
  and verification requirements for code intended for a PR.
- Treat transcript discussions and API critiques as design evidence, not as
  authority for mathematical claims or statements about the current source.
- Verify current source and official documentation before asserting that an
  upstream API, theorem, or behavior still has a particular form.
- Do not stage, commit, push, open a PR, or modify remote settings unless the
  current request authorizes that action.
