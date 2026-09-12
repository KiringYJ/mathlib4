# Source Repository Registry

## Purpose and Status

This is the canonical registry for repositories considered as sources for this
curated downstream library. It records observed identity and intended handling;
it does not by itself authorize adding a Git remote, fetching, copying source,
adding a dependency, merging, committing, or publishing.

The word "source" is used here for any external repository from which material
might be learned, depended on, or integrated. The Git remote literally named
`upstream` is reserved for the mathlib baseline. Other source repositories use
distinct, stable remote names when a later task explicitly adds them.

## Repository Roles

### Destination

- Repository: `KiringYJ/mathlib-fidelity`
- Local remote: `origin`
- URL: `https://github.com/KiringYJ/mathlib-fidelity.git`
- Role: publication destination for this curated fork
- Push policy: push only with explicit authorization

### Active baseline source

- Repository: `leanprover-community/mathlib4`
- Local remote: `upstream`
- URL: `https://github.com/leanprover-community/mathlib4.git`
- Tracked ref: `upstream/master`
- History relationship: shared ancestry; `main` is periodically rebased onto
  `upstream/master` as a maintained Fidelity patch stack
- Integration mode: batched rebase onto `upstream/master`, followed by API
  repair and final-state validation
- Reconciliation state: Git ancestry is authoritative; no separate
  last-reconciled SHA is maintained
- License evidence: the current source tree contains the Apache License 2.0 in
  `LICENSE`; recheck the exact source revision and any file-specific notices at
  each import boundary
- Status: active

## Candidate Sources

The following repositories are a future intake backlog, not accepted sources.
The original registry's repository URLs and default refs were checked with
`git ls-remote --symref` on 2026-09-11. Later additions are checked when they
are recorded; `merely-true/merely-true`, `TauCetiProject/TauCeti`, and the
existing `Vilin97/lean-pool` feed were checked on 2026-09-12. That check
establishes repository identity only. No license compatibility, per-file
provenance, mathematical fidelity, proof, axiom, `sorry`, dependency, overlap,
maintenance, or migration audit is implied. No local remotes have been added
for them, and their moving default refs are not intake revision pins.

Before promoting any row to `accepted`, record its full immutable source commit
and complete the required intake record below. Work through this list at the
maintainer's discretion; its presence creates no completeness or schedule
commitment.

### Lean 3 preservation and reconstruction leads

These projects require theorem-level comparison with the current library before
any source transfer. Their provisional recovery modes and priorities are
tracked in `MIGRATION_BACKLOG.md`; the rows here record source identity only.

| Candidate | Scope to investigate | Observed default ref |
| --- | --- | --- |
| [adamtopaz/lean-acl-pairs](https://github.com/adamtopaz/lean-acl-pairs) | alternating pairs and valuation rings; possible small Lean 3 port pilot | `master` |
| [leanprover-community/lean-liquid](https://github.com/leanprover-community/lean-liquid) | Liquid Tensor Experiment theorem coverage on current condensed and homological-algebra APIs | `master` |
| [leanprover-community/lean-perfectoid-spaces](https://github.com/leanprover-community/lean-perfectoid-spaces) | perfectoid-space, adic-space, and Huber infrastructure requiring current-Mathlib overlap analysis | `master` |
| [dagurtomas/lean-solid](https://github.com/dagurtomas/lean-solid) | solid-abelian-group results requiring semantic comparison with `Mathlib.Condensed.Solid` | `master` |
| [b-mehta/topos](https://github.com/b-mehta/topos) | topos, Lawvere--Tierney topology, and sheafification results requiring overlap analysis | `master` |
| [ianklatzco/flypitch](https://github.com/ianklatzco/flypitch) | existing Lean 4 Flypitch descendant to audit rather than reconstruct from scratch | `master` |

### Established mathlib-downstream leads

These were named in the source conversation and are also identifiable in the
current mathlib downstream registry or directly by repository identity.

| Candidate | Scope to investigate | Observed default ref |
| --- | --- | --- |
| [ImperialCollegeLondon/FLT](https://github.com/ImperialCollegeLondon/FLT) | Fermat's Last Theorem and supporting algebra, number theory, geometry, and representation theory | `main` |
| [leanprover-community/flt-regular](https://github.com/leanprover-community/flt-regular) | Fermat's Last Theorem for regular primes | `master` |
| [fpvandoorn/carleson](https://github.com/fpvandoorn/carleson) | Carleson operators on doubling metric-measure spaces | `master` |
| [teorth/pfr](https://github.com/teorth/pfr) | Polynomial Freiman--Ruzsa formalization | `master` |
| [AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) | prime number theorem and analytic-number-theory infrastructure | `main` |
| [kbuzzard/ClassFieldTheory](https://github.com/kbuzzard/ClassFieldTheory) | class field theory | `main` |
| [leanprover-community/sphere-eversion](https://github.com/leanprover-community/sphere-eversion) | sphere eversion and differential topology | `master` |
| [thefundamentaltheor3m/Sphere-Packing-Lean](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean) | sphere packing in dimension eight | `main` |
| [emilyriehl/infinity-cosmos](https://github.com/emilyriehl/infinity-cosmos) | higher category theory and infinity-cosmoses | `main` |
| [teorth/equational_theories](https://github.com/teorth/equational_theories) | equational theories and universal algebra | `main` |
| [Paul-Lez/PersistentDecomp](https://github.com/Paul-Lez/PersistentDecomp) | decomposition of persistence modules | `master` |
| [RemyDegenne/brownian-motion](https://github.com/RemyDegenne/brownian-motion) | Brownian motion and stochastic-analysis infrastructure | `master` |
| [YijunYuan/HarderNarasimhan](https://github.com/YijunYuan/HarderNarasimhan) | Harder--Narasimhan theory | `paper` |
| [YaelDillies/Toric](https://github.com/YaelDillies/Toric) | toric varieties | `master` |
| [Whysoserioushah/BrauerGroup_new](https://github.com/Whysoserioushah/BrauerGroup_new) | Brauer groups | `main` |
| [mcdoll/DispersiveEquations](https://github.com/mcdoll/DispersiveEquations) | nonlinear dispersive equations | `master` |
| [Ivan-Sergeyev/seymour](https://github.com/Ivan-Sergeyev/seymour) | Seymour decomposition for regular matroids | `main` |
| [leanprover-community/physlib](https://github.com/leanprover-community/physlib) | physics-specific formalization library | `master` |
| [lecopivo/SciLean](https://github.com/lecopivo/SciLean) | scientific computing and applied-mathematics infrastructure | `master` |

### Paper-scale and specialty leads

| Candidate | Scope to investigate | Observed default ref |
| --- | --- | --- |
| [b-mehta/AharoniKorman](https://github.com/b-mehta/AharoniKorman) | counterexample to the Aharoni--Korman conjecture | `master` |
| [b-mehta/exponential-ramsey](https://github.com/b-mehta/exponential-ramsey) | exponential diagonal Ramsey upper bound | `main` |
| [b-mehta/ABC-Exceptions](https://github.com/b-mehta/ABC-Exceptions) | quantitative bounds for the abc exceptional set | `main` |
| [teorth/sendov](https://github.com/teorth/sendov) | Sendov and Phelps--Rodriguez statements and proofs | `master` |
| [alonamaloh/schoenflies-lean](https://github.com/alonamaloh/schoenflies-lean) | Jordan--Schoenflies theorem | `main` |
| [ARGO-LABORATORY/Wolstenholme_1862](https://github.com/ARGO-LABORATORY/Wolstenholme_1862) | Wolstenholme theorem | `main` |
| [0stellensatz/MassFormula](https://github.com/0stellensatz/MassFormula) | Serre mass formulas for totally ramified local-field extensions and supporting finiteness/convergence infrastructure | `master` |
| [ashvin-swaminathan/quartic-invariant](https://github.com/ashvin-swaminathan/quartic-invariant) | quartic invariant of odd-degree binary forms; distinguish paper claims, Lean statements, and computational verification | `main` |
| [karlesmarin/godsil-gutman-lean](https://github.com/karlesmarin/godsil-gutman-lean) | matching polynomials, graph spectra, determinants, and real-rootedness infrastructure; audit theorem inventory and `MathlibPR` overlap | `main` |
| [catskillsresearch/scott1964](https://github.com/catskillsresearch/scott1964) | Scott's measurement structures and linear inequalities; audit source correspondence, separately labelled modern extensions, and comparator proof-hole boundaries | `main` |
| [yawara/odd-order](https://github.com/yawara/odd-order) | Feit--Thompson odd-order theorem; independently audit the claimed proof boundary | `main` |
| [LionSR/TNLean](https://github.com/LionSR/TNLean) | tensor networks and the fundamental theorem of matrix product states | `main` |
| [a-dangelo/Lean-AG](https://github.com/a-dangelo/Lean-AG) | algebraic geometry, including scheme and Krull-dimension material | `main` |
| [mo271/FormalBook](https://github.com/mo271/FormalBook) | proofs from *Proofs from THE BOOK*, with proof-faithfulness as a comparison point | `main` |
| [sinhp/HoTTLean](https://github.com/sinhp/HoTTLean) | metatheory of HoTT and models of dependent type theory | `master` |
| [oliver-butterley/SpectralThm](https://github.com/oliver-butterley/SpectralThm) | spectral theorem for bounded normal operators | `main` |
| [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation) | mathematical logic, including completeness and cut elimination | `master` |
| [YuanheZ/lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory) | statistical learning theory and probability infrastructure | `main` |
| [lean-dojo/LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems) | Millennium Problem statements and supporting infrastructure; do not treat the collection as proofs of the problems | `main` |

### Recent and AI-assisted leads

Claims made by these repositories require the same independent mathematical
and provenance review as any other source. Compilation, generated metadata, or
a repository's own clean-status label is not an admission verdict.

| Candidate | Scope to investigate | Observed default ref |
| --- | --- | --- |
| [merely-true/merely-true](https://github.com/merely-true/merely-true) | permissive AI-generated Lean library with automatic CI-based merging and no manual human review; independently audit statement and definition fidelity, provenance, maintenance stability, overlap, and reusable API before selecting material | `main` |
| [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti) | AI-authored integrated Lean library directed by human roadmaps and adversarial AI review; independently audit definitions, statements, review evidence, attribution, overlap, and adaptation to this fork's design | `main` |
| [mattrobball/BridgelandStability](https://github.com/mattrobball/BridgelandStability) | AI-assisted Lean 4 formalization of Bridgeland stability conditions and claimed paper-result coverage; independently audit statement correspondence, trusted boundary, axioms, `sorry`s, and generated artifacts | `main` |
| [marcmorningstar/lean4-ergodic-theory](https://github.com/marcmorningstar/lean4-ergodic-theory) | self-described smooth ergodic theory centered on Oseledets, with entropy and Livšic developments; audit theorem coverage and current-library overlap | `main` |
| [will1491/RiemannDynamics](https://github.com/will1491/RiemannDynamics) | ongoing complex-dynamics, Riemann-surface, Teichmüller, and hyperbolic-geometry development; audit headline claims and vendored dependencies | `main` |
| [MerLeanProver/ACMaxConjecture](https://github.com/MerLeanProver/ACMaxConjecture) | claimed ACMAX graph-conjecture formalization; independently audit source correspondence, exports, comparator, and trusted boundary | `main` |
| [tadamcz/mean-value-problem](https://github.com/tadamcz/mean-value-problem) | AI-assisted claimed disproof of Smale's mean-value conjecture with `K = 1`; audit exact negation, witness, and comparator boundary | `main` |
| [tadamcz/erdos548](https://github.com/tadamcz/erdos548) | AI-assisted claimed proof of Erdős Problem 548; audit source statement, mathematical fidelity, comparator, and provenance | `main` |
| [tadamcz/erdos571](https://github.com/tadamcz/erdos571) | AI-assisted claimed proof of Erdős Problem 571; audit source statement, mathematical fidelity, comparator, and provenance | `main` |
| [Yuren-Tang/erdos-306](https://github.com/Yuren-Tang/erdos-306) | claimed proof of Erdős Problem 306 conditional on two named Rosser--Schoenfeld axioms; preserve and independently audit that boundary | `main` |
| [openai/NavierStokesAndEuler](https://github.com/openai/NavierStokesAndEuler) | Navier--Stokes and Euler statement/proof artifacts | `main` |
| [openai/ten-proofs](https://github.com/openai/ten-proofs) | collection of ten mathematics and theoretical-CS formalizations | `main` |
| [openai/cdc-lean](https://github.com/openai/cdc-lean) | cycle double cover formalization | `main` |
| [anthropics/formal-math](https://github.com/anthropics/formal-math) | collection of separately structured formal-mathematics projects | `main` |
| [anthropics/fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem) | claimed Fermat's Last Theorem proof; independently verify the statement and trusted proof boundary | `main` |
| [openai/PrimeGaps186](https://github.com/openai/PrimeGaps186) | prime-gap formalization; preserve and verify any conditional axioms rather than presenting it as unconditional | `main` |
| [openai/LongGapsBetweenPrimes](https://github.com/openai/LongGapsBetweenPrimes) | long gaps between primes | `master` |
| [Vilin97/Clawristotle](https://github.com/Vilin97/Clawristotle) | branch-structured AI-assisted projects, including Vlasov--Maxwell--Landau and Grothendieck-vanishing work | `main` |
| [gotrevor/lean-gallery](https://github.com/gotrevor/lean-gallery) | curated formalization collection; independently verify each included module | `main` |
| [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) | statement and scaffold corpus; use primarily as a discovery source unless proofs are separately established | `main` |
| [ImperialCollegeLondon/AnnalsChallenge](https://github.com/ImperialCollegeLondon/AnnalsChallenge) | formalized Annals theorem statements with proof obligations; catalogue rather than completed proof source | `main` |

### Discovery feeds

These repositories are indexes or aggregates, not proof authorities. Use them
to find underlying projects, then resolve and audit the original repository and
revision before adding it as a candidate source.

| Feed | Use | Observed default ref |
| --- | --- | --- |
| [dzackgarza/formalization-corpus](https://github.com/dzackgarza/formalization-corpus) | searchable cross-repository formalization index for discovery and reuse checks | `main` |
| [Vilin97/lean-pool](https://github.com/Vilin97/lean-pool) | aggregate of formalization projects with source provenance; follow each entry to its original source | `main` |

### Identity-resolution and discovery backlog

The conversation also mentioned the following leads without enough stable
repository identity to enter them above. Resolve the exact current repository,
revision, and scope before promoting them to candidate rows:

- formalizations of the Weil converse theorem and Dirichlet nonvanishing;
- an `FRI` formalization project;
- LeanProject and Lean Reservoir project catalogues;
- repositories using `formalization.yaml` or the Palomar template as discovery
  feeds.
- cross-prover versions of Flyspeck, the computation of
  `pi_4(S^3)`, and the Four Color Theorem; identify the exact maintained source
  and audit foundation compatibility before treating any as a Lean migration
  candidate.

Discovery feeds are indexes, not trusted proof sources. Follow each pointer to
the underlying repository and perform the ordinary intake audit.

## Required Intake Record

Promote a candidate to `accepted`, or add an active source, only after recording
all applicable fields:

```text
Source ID:
Repository owner/name:
Canonical URL:
Local remote name: none | <name>
Source revision:
Tracked refs:
History relationship: shared | unrelated | unknown
License and version:
License evidence at revision:
NOTICE / attribution obligations:
Third-party or per-file exceptions:
Intended mode: reference-only | dependency | cherry-pick | source-port
Mathematical scope:
Proof status: verified | conditional | incomplete | unknown
Axioms / sorry / generated-code status:
Overlap and deduplication plan:
Provenance mapping:
Migration notes:
Verification:
Status: candidate | accepted | migrating | integrated | declined | paused
```

An `accepted` record means selected for integration; it does not mean the
source's current API is canonical. An `integrated` record requires completed
provenance, migration, and verification evidence.

## Intake Procedure

1. Identify the exact repository and immutable source revision.
2. Inspect the license at that revision, per-file headers, bundled third-party
   material, and any `NOTICE` or attribution requirements. If permission is
   absent, unclear, or incompatible, keep the source reference-only pending a
   separate license review.
3. Audit the mathematical statements, assumptions, proof dependencies, axioms,
   `sorry`s, generated artifacts, and fidelity to the cited mathematics.
4. Search the maintained tree and other candidates for equivalent declarations
   before importing another version of the same concept.
5. Choose the integration mode. Multiple Git remotes are useful for discovery
   and shared-history review, but independent histories are normally source
   ports or Lake dependencies, not unrelated-history merges.
6. Record file- or declaration-level provenance and preserve applicable notices
   before editing the imported material.
7. Migrate accepted content to the canonical mathematical API and repository
   conventions. Presentation problems are integration work, not retroactive
   evidence that the mathematics was invalid.
8. Run mathematical and technical review at the final integrated state, then
   update the record to `integrated` only when the evidence is complete.

## License References

License compatibility must be decided for the exact source and distribution;
this checklist is not a complete legal determination.

- [Apache License 2.0, section 4](https://www.apache.org/licenses/LICENSE-2.0.html)
  states its redistribution conditions, including providing the license,
  marking modified files, retaining applicable notices, and carrying forward
  applicable `NOTICE` attribution.
- [GitHub's repository licensing documentation](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/customizing-your-repository/licensing-a-repository)
  explains that public visibility without a license does not grant general
  permission to reproduce, distribute, or create derivative works.
