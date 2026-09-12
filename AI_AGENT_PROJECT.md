# Project-Specific Agent Context

## Purpose

This fork is a personal, maintainer-curated downstream distribution of mathlib.
It uses the upstream implementation and theorem base while developing an
independent, mathematician-facing library whose public API prioritizes
mathematical fidelity and quality of life.

Fork-only changes are not intended for submission to upstream. Do not preserve,
split, or rewrite them merely for upstream pull-request acceptability. Upstream
remains a source of useful code and updates, not the target design authority for
this fork.

`FORK_DESIGN.md` is the human-facing source of truth for the fork's design
philosophy and deferred foundational roadmap. In particular, it records the
strict-totalization direction without authorizing the total-inverse migration.

The policies below are project-local overrides. `main` is this fork's canonical
workspace source of truth and default branch. The upstream `master` branch is
tracked directly as `upstream/master`; this fork does not keep a local
`master` mirror or publish `origin/master`.

## Branch Model

- `main` is the canonical personal branch, GitHub default branch, and daily
  driver. It is the latest reconciled upstream baseline plus a maintained stack
  of Fidelity commits. Periodic upstream reconciliation may rewrite its
  published history; `main` is not an append-only branch. The agent-workbench
  and fork-design files are tracked only on this personal line of development.
- `upstream/master` is the read-only remote-tracking reference for the official
  `leanprover-community/mathlib4:master` baseline. Do not recreate a local
  `master` mirror or publish an `origin/master` branch merely to mirror it.
- `palomar/<slug>` branches are separately maintained delivery branches for
  Palomar Registry projects. Keep project-specific theorem, source, provenance,
  and review records inside the corresponding branch. These branches are not
  part of the `main` Fidelity patch stack, alternative defaults, or general
  development branches; do not merge them wholesale into `main` merely to
  synchronize branch history.
- `exp/<slug>` may be used for work whose mathematical or API direction is not
  yet settled.
- Formal releases are published as tags. A published release tag is an
  immutable snapshot and is not moved when `main` is rebased.
- External pull requests target `main` from contributor-owned branches.
  Contributor branch names are not part of this repository's maintained branch
  taxonomy.

Do not infer authorization to push from a fetch, sync, or local branch update.
All pushes go to `origin`; never push to `upstream`.

Keep logically independent changes in separate, semantically coherent commits
on `main`. Those commits form the maintained Fidelity patch stack and must stay
reviewable and replayable across upstream rebases.

## Mathlib Baseline Reconciliation Workflow

Routine upstream reconciliation uses rebase, not upstream merge commits. Batch
reconciliations at a justified cadence rather than rewriting `main` for every
small upstream movement.

1. Require a clean working tree and fetch `origin`. Capture the exact
   `origin/main` object ID as `<expected-origin-main>` and verify that it is an
   ancestor of local `main`. Local-ahead Fidelity commits are allowed; stop if
   the remote tip is not incorporated locally or the histories have diverged.
2. Before rewriting `main`, inventory open pull requests that target it. Retain
   each old merge base, head ref, and head object ID ephemerally so later updates
   can replay only the contributor commits and can use a separate exact lease.
3. Fetch `upstream` and inspect the new `upstream/master`. Avoid an unnecessary
   base rewrite during active review; when a substantial pull request is close
   to merger, the maintainer may temporarily freeze reconciliation.
4. Rebase `main` onto `upstream/master`. Do not merge `upstream/master` into
   `main` in the routine workflow.
5. Resolve conflicts and repair API fallout according to this fork's
   mathematical and API design while retaining sound upstream improvements.
6. Run checks proportional to every affected module at the final rebased state.
   Upstream's successful checks do not validate fork-specific conflict repairs.
7. After explicit publication authorization, confirm that branch rules permit
   the rewrite and push with
   `git push --force-with-lease=refs/heads/main:<expected-origin-main> origin main:refs/heads/main`.
   Never use bare `--force-with-lease` or plain `--force`; if the explicit lease
   fails, stop and re-evaluate the remote changes rather than overwriting them.
8. Verify that local `main`, `origin/main`, and the live remote ref resolve to
   the same commit.

Do not maintain a separate last-reconciled SHA file or ledger field. Git
ancestry records the reconciled baseline. The lease and open-PR object IDs are
ephemeral transaction state, not persistent reconciliation metadata. Never open
or prepare an upstream pull request, and never push to `upstream`.

## Contributions and Curated External Source Intake

This repository accepts external pull requests that follow its mathematical,
API, provenance, licensing, testing, and review policies. Policy compliance
makes a contribution eligible for review; it does not guarantee merger. The
maintainer may request revisions or decline a contribution because of scope,
duplication, maintenance cost, or conflict with the fork's design direction.

### Moving `main` and open pull requests

Contributors must expect that periodic upstream reconciliation can change the
merge base of an open pull request. Maintainers should batch those rewrites,
avoid unnecessary churn during active review, and may freeze reconciliation
while a substantial pull request is close to merger.

Contributors own the mathematical content, original implementation, and
responses to substantive review. Maintainers own branch maintenance and
integration fallout caused solely by upstream reconciliation or fork-wide
canonical API migrations. When the pull request author has granted maintainer
access, a maintainer may prepare the rebase and resolve that repository-driven
fallout. A force-update may be used only after verifying that the hosting
service and branch rules permit it. This policy is not standing authorization
to write to a contributor's branch: both the author's branch permission and
explicit authorization for the current operation remain required. If either is
unavailable, coordinate the update with the contributor. If maintainer edits
also expose workflow-secret access, treat that access as security-sensitive and
do not use it beyond the authorized integration work.

When updating a pull request after `main` moves, use its retained old merge base
to replay only the contributor range, normally with
`git rebase --onto <new-main> <old-merge-base> <pr-head>`. Do not naively rebase
the old-base branch in a way that replays the obsolete Fidelity stack. Before a
permitted force-update of the pull request branch, use the retained pre-work
head object ID as the expected value in a separate explicit force-with-lease.
If the live head has changed, stop, incorporate the contributor's new commits,
and begin a new update transaction with a newly captured head object ID; do not
merely recapture the advanced head and overwrite it.

External formalizations may be proposed through a pull request or selected by
the maintainer from other repositories. A suggestion, public repository, or
valid result does not by itself create a review deadline or permanent backlog.
Intake may slow or stop when the available audit and migration capacity is
exhausted.

Do not reject mathematically valid and legally ingestible content merely because
it is small, niche, or presently uses a poor API. Separate admission from
canonicalization: audit the mathematical content and provenance first, then
migrate selected material to this fork's faithful API and conventions. API,
namespace, import, or proof-style defects are maintainer integration work. They
do not justify preserving a second noncanonical public interface.

Before copying or adapting external material, verify the exact source revision,
license and redistribution conditions, per-file authorship, third-party content,
`NOTICE` obligations, axioms, `sorry`s, generated artifacts, mathematical
status, and overlap with existing declarations. Record the source and every
integration in `UPSTREAMS.md`. If permission is absent or unclear, retain only a
reference until a separate license review establishes an authorized path.

Multiple Git remotes may be used to track sources, but remotes do not imply
admission or merge authority. Shared-history forks may support selective
cherry-picks or ports. Independent repositories should normally remain Lake
dependencies or be migrated through reviewed source integration; do not merge
unrelated histories merely to ingest their content.

## Mathematician-Facing Design Commitments

Mathematical fidelity and API quality are coequal requirements. Do not trade
away intended domains or hypotheses for convenience, and do not accept
dependent-type plumbing as the necessary price of fidelity. Preserve genuine
proof obligations while making routine evidence construction, propagation,
rewriting, and diagnostics library responsibilities.

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
should be retained when deciding API boundaries. Prefer a useful concrete
interface that has survived real use over premature generalization. Generalize
after downstream cases demonstrate the reusable structure.

Treat a mathematically sound, faithful, and conceptually natural proof as an
API test. If such a proof remains complicated or tedious to express in Lean,
that is an API design failure to diagnose and repair, not ordinary downstream
cost. Change the representation, theorem shapes, normal forms, facades,
coercions, elaboration, diagnostics, or automation as appropriate so the formal
proof can follow the mathematics. A shorter proof does not count as an
improvement if it weakens the statement, hides hypotheses or domains, or relies
on totalized fallback semantics.

Preserve strong upstream substrate when it is mathematically and technically
sound. This fork is not different for the sake of being different; it changes
interfaces where actual formalization exposes semantic or ergonomic friction.

For a mathematically partial operation, the strict public API must expose its
domain through an input type, proof argument, or explicit partiality. A total
extension may exist behind a proved boundary or under an explicit name, but it
must not silently inherit the ordinary mathematical name and erase definedness
from the type. Automation may discharge real obligations; it must fail clearly
rather than fall back to a reachable totalized operation.

See `FORK_DESIGN.md` for the complete design contract, including the rule that
source-expression domain obligations are checked before simplification, the
strict-interface versus strict-implementation distinction, and the deferred
total-inverse prototype and acceptance criteria.

## Working API Heuristics

These are review questions, not unconditional rules. Establish them against
concrete use cases before redesigning existing code.

- Is there a clear normal form for statements and theorem search?
- Does a coercion or typeclass hide a mathematical choice that users routinely
  need to vary explicitly?
- Does a partial operation preserve its domain obligation in the public type,
  proof arguments, or an explicit partiality type?
- Can routine evidence be constructed and propagated automatically without
  concealing a genuine unresolved obligation?
- Can simplification, coercion insertion, or instance search erase a domain
  condition or silently select a totalized fallback?
- If a total extension is independently useful, does its name and documentation
  identify the extension rather than reuse the partial mathematical operation's
  name?
- Can a thin facade improve semantic fidelity without duplicating a parallel
  theorem ecosystem?
- If a better public interface replaces an established one, is there a
  deliberate migration path that distinguishes interface progress from removal
  of totalized implementation dependencies?
- Does generated proof glue merely conceal an ontology mismatch? Automation
  and language models can assist discovery, but should not be used as evidence
  that a human-facing interface is already adequate.

Treat these as hypotheses to test through downstream code, not as blanket
claims about every mathlib module or maintainer. Keep criticism technical and
specific; do not put personal attacks in repository history, commits, issues,
or other project records.

## Broad API Refactor Protocol

For an explicitly authorized public-API canonicalization:

1. Inventory the existing representations, notation, theorem families,
   instances, automation, and structurally different downstream consumers.
2. Separate ambient objects, propositions, and proof-carrying domains before
   choosing canonical syntax. State one normal form for each intended context
   and add regression tests for definitional equalities between retained
   surfaces.
3. Prototype the replacement in real consumers. Closure-heavy proofs should
   use the operations of the structure that owns the invariant; cross a
   predicate-membership bridge only at an interface that genuinely requires
   the other form.
4. When compatibility is explicitly out of scope, remove obsolete notation,
   aliases, ambient-only instances, and legacy subtype spellings across the
   repository. Do not preserve them merely to conceal an incomplete migration.
5. Rename declarations when their mathematical category changes, not merely
   their typography. Keep established terminology primary and implementation
   class names out of the public mathematical language.
6. During iteration, build the narrow affected modules. At the final source
   state, run `lake build`,
   `lake build MathlibTest Archive Counterexamples Wanted`, `lake test`,
   `lake exe mk_all --check`, and `git diff --check` for a cross-cutting
   refactor of this scale.
7. Add repository-wide negative scans for every removed surface, obsolete
   theorem name, compatibility shim, legacy representation, and newly added
   `sorry` or `admit`. A later core edit or byte-level normalization invalidates
   affected evidence and requires the relevant checks to be rerun.

When a style tool traverses transitive imports, distinguish errors introduced
by the current diff from pre-existing repository debt. Fix in-scope new errors
and report inherited failures accurately without expanding the refactor.

## Architecture

- `Mathlib/` contains library modules.
- `Mathlib.lean` is the generated import root and must be refreshed when new
  modules are added.
- `MathlibTest/`, `Archive/`, `Counterexamples/`, and `scripts/` provide tests,
  historical material, examples, and repository tooling.
- `FORK_DESIGN.md` records the fork's design philosophy and deferred roadmap.
- `UPSTREAMS.md` records external source identity, license evidence,
  provenance, integration mode, and status.
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

Run `lake exe mk_all` when adding a new module. Reuse relevant upstream linter
and documentation checks when they remain applicable to the affected area.

## Important Files and Directories

- `README.md`: fork overview, branch model, setup, contribution policy, and
  upstream resource links.
- `FORK_DESIGN.md`: fork purpose, API commitments, and deferred foundational
  migration plans.
- `UPSTREAMS.md`: canonical source-repository and provenance registry.
- `.github/CONTRIBUTING.md`: contribution requirements for pull requests to
  this fork and the separate upstream boundary.
- `.github/PULL_REQUEST_TEMPLATE.md`: fork-specific submission prompts,
  verification checklist, and moving-base disclosure.
- `lakefile.lean` and `lean-toolchain`: project and Lean toolchain definitions.
- `.agent-workbench.yaml`: human-owned desired workbench configuration.
- `.agent-workbench.lock.json`: generated sync provenance and checksum ledger.

## Domain Terms

- **mathlib baseline**: `leanprover-community/mathlib4`, tracked by the local
  remote named `upstream`.
- **origin**: the personal fork `KiringYJ/mathlib-fidelity`.
- **daily driver**: `main`, the complete preferred working version and default
  branch.
- **source repository**: an external repository considered for reference,
  dependency, or curated integration; it is not automatically an authority or
  admitted dependency.
- **curated integration**: selection, audit, deduplication, faithful API
  migration, provenance capture, and final verification of external material.
- **mathematician-facing facade**: a thin public interface that exposes a
  mathematical concept naturally while reusing a sound generic core.
- **strict public API**: an interface whose ordinary mathematical operations
  expose their domains instead of relying on silent fallback values.
- **explicit total extension**: a deliberately total operation whose name and
  documentation identify the chosen extension outside the ordinary domain.

## Workspace Configuration

All agent-workbench managed paths are shared configuration for the personal
`main` branch and should be tracked there. Do not hide them through
`.git/info/exclude` or `.gitignore`.

Personal settings, credentials, caches, absolute machine paths, and runtime
state remain untracked. Future full syncs may update generated managed files
and the provenance ledger, but must never rewrite this project file.

## Project-Specific Constraints

- Inspect the current branch before editing. Personal changes belong on `main`
  or an explicitly selected topic branch; use `upstream/master` only as the
  official baseline reference.
- Keep hooks enabled and follow the fork's naming, style, documentation, and
  verification requirements. Upstream conventions are useful defaults only
  where they do not conflict with `FORK_DESIGN.md`.
- Treat transcript discussions and API critiques as design evidence, not as
  authority for mathematical claims or statements about the current source.
- Verify current source and official documentation before asserting that an
  upstream API, theorem, or behavior still has a particular form.
- Do not add source remotes, dependencies, or imported code merely because a
  repository is mentioned. Require an explicit intake task and update
  `UPSTREAMS.md` from verified evidence.
- Never infer redistribution permission from a public repository alone. Keep
  sources without a verified compatible license reference-only pending review,
  and preserve all applicable authorship, license, modification, and `NOTICE`
  records when integration is authorized.
- Do not start the deferred total-inverse migration merely because its roadmap
  is recorded. It requires a separate explicit task and prototype evidence.
- Do not stage, commit, push, open a PR, or modify remote settings unless the
  current request authorizes that action. No project change is intended for an
  upstream PR.
