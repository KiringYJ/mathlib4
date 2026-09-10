# Project-Specific Agent Context

## Purpose

This fork is a personal downstream distribution of mathlib. It uses the
upstream implementation and theorem base while developing an independent,
mathematician-facing library whose public API prioritizes mathematical fidelity
and quality of life.

Fork-only changes are not intended for submission to upstream. Do not preserve,
split, or rewrite them for pull-request acceptability. Upstream remains a source
of useful code and updates, not the target design authority for this fork.

`FORK_DESIGN.md` is the human-facing source of truth for the fork's design
philosophy and deferred foundational roadmap. In particular, it records the
strict-totalization direction without authorizing the total-inverse migration.

The policies below are project-local overrides. In particular, generic
agent-workbench references to `main` as the workspace source of truth do not
apply: this fork has no `main` branch.

## Branch Model

- `master` is a protected mirror of `leanprover-community/mathlib4:master`.
  It must contain no personal commits, workbench files, or other fork-only
  changes. Update local `master` only by fetching `upstream` and fast-forwarding
  it to `upstream/master`.
- `dev` is the canonical personal branch and daily driver. It contains the
  complete preferred working version: the reconciled upstream base plus all
  fork-only improvements and research developments. The agent-workbench and
  fork-design files are tracked only on this personal line of development.
- `exp/<slug>` may be used for work whose mathematical or API direction is not
  yet settled.
- No `pr/<slug>` branch category is part of this project's workflow. Do not
  prepare or export fork changes for upstream pull requests.

After an explicitly authorized publication, `origin/master` should point to
the same commit as `upstream/master`. Do not infer authorization to push from a
fetch, sync, or local branch update. All pushes go to `origin`; never push to
`upstream`.

Keep logically independent changes in separate, semantically coherent commits
on `dev`. This makes long-term upstream reconciliation, review, and rollback
auditable even when the personal branch has accumulated many changes.

## Upstream Reconciliation Workflow

1. Fetch `upstream`, switch to `master`, and run
   `git merge --ff-only upstream/master`.
2. Verify that `master` and `upstream/master` resolve to the same commit.
3. Reconcile the updated base with `dev` only in an authorized sync task. Choose
   merge or rebase from the current publication state and repository history;
   do not rewrite published history implicitly.
4. Resolve conflicts according to this fork's mathematical and API design,
   while retaining sound upstream improvements when possible.
5. Run checks proportional to every affected module at the final reconciled
   state. Upstream's successful checks do not validate fork-specific conflict
   resolutions.

After an explicitly authorized publication, push only to `origin`. Never open
or prepare an upstream pull request, and never push to `upstream`.

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

## Architecture

- `Mathlib/` contains library modules.
- `Mathlib.lean` is the generated import root and must be refreshed when new
  modules are added.
- `MathlibTest/`, `Archive/`, `Counterexamples/`, and `scripts/` provide tests,
  historical material, examples, and repository tooling.
- `FORK_DESIGN.md` records the fork's design philosophy and deferred roadmap.
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

- `README.md`: upstream setup, build, and contribution entry points.
- `FORK_DESIGN.md`: fork purpose, API commitments, and deferred foundational
  migration plans.
- `.github/CONTRIBUTING.md`: link to the current upstream contribution guide.
- `lakefile.lean` and `lean-toolchain`: project and Lean toolchain definitions.
- `.agent-workbench.yaml`: human-owned desired workbench configuration.
- `.agent-workbench.lock.json`: generated sync provenance and checksum ledger.

## Domain Terms

- **upstream**: `leanprover-community/mathlib4`.
- **origin**: the personal fork `KiringYJ/mathlib4`.
- **daily driver**: `dev`, the complete preferred working version.
- **mathematician-facing facade**: a thin public interface that exposes a
  mathematical concept naturally while reusing a sound generic core.
- **strict public API**: an interface whose ordinary mathematical operations
  expose their domains instead of relying on silent fallback values.
- **explicit total extension**: a deliberately total operation whose name and
  documentation identify the chosen extension outside the ordinary domain.

## Workspace Configuration

All agent-workbench managed paths are shared configuration for the personal
`dev` branch and should be tracked there. Do not hide them through
`.git/info/exclude` or `.gitignore`. Do not copy, merge, or cherry-pick them into
the protected `master` mirror.

Personal settings, credentials, caches, absolute machine paths, and runtime
state remain untracked. Future full syncs may update generated managed files
and the provenance ledger, but must never rewrite this project file.

## Project-Specific Constraints

- Inspect the current branch before editing. Never make personal changes on
  `master`.
- Keep hooks enabled and follow the fork's naming, style, documentation, and
  verification requirements. Upstream conventions are useful defaults only
  where they do not conflict with `FORK_DESIGN.md`.
- Treat transcript discussions and API critiques as design evidence, not as
  authority for mathematical claims or statements about the current source.
- Verify current source and official documentation before asserting that an
  upstream API, theorem, or behavior still has a particular form.
- Do not start the deferred total-inverse migration merely because its roadmap
  is recorded. It requires a separate explicit task and prototype evidence.
- Do not stage, commit, push, open a PR, or modify remote settings unless the
  current request authorizes that action. No project change is intended for an
  upstream PR.
