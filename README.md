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
  driver.
- `upstream/master` is the remote-tracking reference for the official mathlib
  baseline. This fork does not keep a local `master` mirror or publish
  `origin/master`.
- `palomar/<slug>` branches contain separately maintained Palomar Registry
  delivery artifacts. They are not alternative default or general development
  branches and should not be merged wholesale into `main` merely to synchronize
  history.
- `exp/<slug>` may be used for mathematically or API-uncertain experiments.

All publication goes to this fork's `origin`; nothing in this repository
authorizes pushes or pull requests to upstream. See
[AI_AGENT_PROJECT.md](AI_AGENT_PROJECT.md) for the complete maintenance policy.

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

This fork deliberately evolves independently of upstream's public API. Pin an
exact reviewed commit rather than a moving branch:

```lean
require mathlib from git
  "https://github.com/KiringYJ/mathlib-fidelity.git" @ "<commit-sha>"
```

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
