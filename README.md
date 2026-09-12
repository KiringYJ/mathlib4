# mathlib-fidelity

`mathlib-fidelity` is a maintainer-curated downstream distribution of
[mathlib](https://github.com/leanprover-community/mathlib4). It retains
mathlib's implementation and theorem base while developing an independent,
mathematician-facing library whose public API prioritizes mathematical fidelity
and quality of life.

External contributions to this fork are welcome through pull requests that
target `main` and follow the repository policy. Fork-only changes are developed
for this distribution and are not prepared for submission to upstream.
Upstream remains a source of sound implementation, theorems, and updates, but
it is not the design authority for this fork.

## Design priorities

- Represent genuinely partial mathematical operations with explicit domains or
  explicit partiality rather than silent fallback values.
- Prefer established mathematical vocabulary and discoverable public APIs over
  representation-driven interfaces.
- Treat natural formal proofs and real downstream formalizations as tests of
  API quality.
- Admit external formalizations through explicit mathematical, licensing,
  provenance, and implementation review.

These are design commitments, not claims that every inherited interface has
already been migrated. See [FORK_DESIGN.md](FORK_DESIGN.md) for the complete
design contract and deferred roadmap.

## Branch model

- `main` is the canonical personal branch, GitHub default branch, and daily
  driver. It is the latest reconciled upstream baseline plus the maintained
  Fidelity patch stack, and its history may be rewritten by periodic upstream
  rebases.
- `upstream/master` is the remote-tracking reference for the official mathlib
  baseline. This fork does not keep a local `master` mirror or publish
  `origin/master`.
- `palomar/<slug>` branches contain separately maintained Palomar Registry
  delivery artifacts. They are not alternative default or general development
  branches and should not be merged wholesale into `main` merely to synchronize
  history.
- `exp/<slug>` may be used for mathematically or API-uncertain experiments.
- Formal releases are immutable tags and are not moved when `main` is rebased.

All publication goes to this fork's `origin`; nothing in this repository
authorizes pushes or pull requests to upstream. See
[AI_AGENT_PROJECT.md](AI_AGENT_PROJECT.md) for the complete maintenance policy.

## Upstream reconciliation

`main` is intentionally rebaseable rather than append-only. Maintainers batch
upstream reconciliation, avoid unnecessary base rewrites during active pull
request review, and may temporarily freeze reconciliation while a substantial
pull request is close to merger. The captured `origin/main` tip must already be
an ancestor of local `main`; unpublished local Fidelity commits are allowed,
but remote-only or divergent history stops the reconciliation. The routine
publication shape is:

```shell
git fetch origin
expected_origin_main="$(git rev-parse refs/remotes/origin/main)"
git fetch upstream
git rebase upstream/master
# repair API fallout and validate
git push --force-with-lease="refs/heads/main:${expected_origin_main}" \
  origin main:refs/heads/main
```

These are maintainer operations and still require explicit publication
authorization. Before rewriting `main`, maintainers inventory open pull requests
and retain their old merge bases and head object IDs ephemerally. Bare
`--force-with-lease` and plain `--force` are not permitted. No separate
last-reconciled SHA is maintained; Git ancestry records the reconciled upstream
baseline.

## Getting started

Install Lean and the supporting tools using the
[upstream mathlib instructions](https://leanprover-community.github.io/get_started.html),
then clone and build this fork:

```shell
git clone https://github.com/KiringYJ/mathlib-fidelity.git
cd mathlib-fidelity
git remote add upstream https://github.com/leanprover-community/mathlib4.git
git fetch upstream
lake exe cache get
lake build
```

For a focused build or the test suite:

```shell
lake build Mathlib.Import.Path
lake test
```

Run `lake exe mk_all` after adding a new Mathlib module so that `Mathlib.lean`
remains current.

## Using the fork as a dependency

This fork deliberately evolves independently of upstream's public API. For a
durable dependency, pin an immutable formal release tag rather than the moving
`main` branch:

```lean
require mathlib from git
  "https://github.com/KiringYJ/mathlib-fidelity.git" @ "<release-tag>"
```

An exact commit from `main` is suitable for short-lived evaluation, but a later
rebase may make an untagged old commit unreachable. Do not treat such a commit
as a durable published release.

The upstream
[dependency guide](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)
still applies to the surrounding Lake project setup.

## Contributing

Pull requests to this fork are welcome when they follow the mathematical
fidelity, API, source, licensing, provenance, testing, and review requirements
in the [contribution guide](.github/CONTRIBUTING.md). Meeting those requirements
makes a contribution eligible for review but does not guarantee merger;
maintainers may request revisions or decline work because of scope,
duplication, maintenance cost, or design direction.

Because `main` may be periodically rebased, an open pull request may need a new
base. Maintainers batch reconciliation and may handle repository-driven rebase
or canonical-API fallout when the contributor grants branch access; contributors
remain responsible for the substance of their contribution. See the contribution
guide for the permission and security boundaries.

External formalizations may arrive either through a pull request or through
maintainer-led curated intake. Contributions to this fork are not automatically
prepared, submitted, or forwarded as upstream mathlib pull requests.

## Project records

- [FORK_DESIGN.md](FORK_DESIGN.md) records the fork's mathematical and API
  design philosophy.
- [MIGRATION_BACKLOG.md](MIGRATION_BACKLOG.md) tracks selected external
  formalization recovery and reconstruction work.
- [UPSTREAMS.md](UPSTREAMS.md) records external source identity, licensing,
  provenance, integration mode, and status.
- [AI_AGENT_PROJECT.md](AI_AGENT_PROJECT.md) defines the repository workflow,
  branch policy, and verification requirements.

## Upstream resources

- [mathlib repository](https://github.com/leanprover-community/mathlib4)
- [Installation and learning resources](https://leanprover-community.github.io/get_started.html)
- [Generated mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Upstream contribution guide](https://leanprover-community.github.io/contribute/)
- [Lean community Zulip](https://leanprover.zulipchat.com)

## License

This repository is distributed under the [Apache License 2.0](LICENSE).
