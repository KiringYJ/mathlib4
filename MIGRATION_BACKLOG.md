# External Formalization Recovery Backlog

## Status and scope

This is a planning inventory for mathematics previously formalized outside the
current library. It does not accept a source, certify its mathematics or
license, authorize an import, or promise a schedule. `UPSTREAMS.md` is the
canonical source registry; every intake still requires an immutable revision
and the complete audit recorded there.

Repository identities and default refs below were checked with `git ls-remote
--symref` on 2026-09-11. Moving refs are navigation evidence, not intake pins.
Project status and Mathlib overlap can change, so every recovery task must
repeat the descendant and coverage search at its start. Failure to find a port
is not proof that none exists.

Use the recovery modes defined in `FORK_DESIGN.md`:

- **port** for a Lean development whose mathematical organization remains
  suitable;
- **reconstruction** for selected theorem coverage that must be rebuilt on
  current foundations and APIs; and
- **reformalization** for results coming from another prover or a materially
  different foundation.

The unit of preservation is an audited mathematical statement together with
its hypotheses, constructions, trusted proof boundary, and correspondence to a
current declaration. File counts, commit counts, matching names, and successful
syntax translation are not acceptance criteria.

## Recovery gates

Before implementation, each candidate must pass these gates:

1. Identify the exact source revision and all plausible maintained descendants.
2. Audit theorem statements, axioms, `sorry`s, generated artifacts, and the
   trusted proof boundary.
3. Establish license compatibility, file-level provenance, attribution, and
   any `NOTICE` obligations.
4. Map the source theorem DAG to current Mathlib and distinguish surviving,
   superseded, unmatched, and differently stated nodes.
5. Select port, reconstruction, or reformalization and design the canonical
   mathematician-facing API from current evidence.
6. Set theorem-level acceptance targets and validate them end to end on the
   final current-library state.

## Priority A -- pilot and flagship work

### `adamtopaz/lean-acl-pairs` -- port pilot

The source is a Lean 3 `leanpkg` project about alternating pairs and valuation
rings. Its bounded scope and identifiable principal results make it a candidate
for testing the intake, API-canonicalization, and provenance workflow before a
larger reconstruction. No Lean 4 descendant is recorded here; repeat a targeted
search before treating a new port as necessary.

Next gate: pin a revision, audit the main and converse statements and proof
boundary, verify licensing and per-file provenance, then measure overlap with
current valuation and linear-algebra APIs.

### `leanprover-community/lean-liquid` -- flagship reconstruction

The Lean 3 source records `liquid_tensor_experiment` as its final challenge
theorem and contains a blueprint plus a substantial `src/for_mathlib` layer.
Current Mathlib already has condensed sets, condensed modules, limits, and a
`Mathlib/Condensed/Solid.lean` development, so preserving the mathematics does
not mean translating the historical source tree.

The acceptance target is a current theorem proved to correspond to the source
`liquid_tensor_experiment`, with its hypotheses, constructions, and proof
status independently audited. That correspondence is pending; this entry does
not certify the historical statement or claim that current Mathlib lacks every
required theorem.

Next gate: map the source blueprint and theorem DAG to current condensed and
homological-algebra declarations, identify the unmatched mathematical layer,
and design a staged reconstruction whose final target is the audited theorem
correspondence.

### `leanprover-community/lean-perfectoid-spaces` -- coverage audit, then reconstruction

The source is a Lean 3 `leanpkg` development of perfectoid spaces. The current
tree contains `Mathlib/RingTheory/Perfectoid/BDeRham.lean`,
`FontaineTheta.lean`, and `Untilt.lean`; a source search found references to
adic spaces but no current declarations named `AdicSpace`, `HuberRing`, or
`HuberPair`. Names alone do not establish mathematical absence or equivalence.

Next gate: compare the old Huber, adic-space, and perfectoid-space layers
declaration by declaration with current valuation, topology, adic, and
perfectoid infrastructure. Reconstruct only the established unmatched layer.

## Priority B -- theorem-level archaeological audits

### `dagurtomas/lean-solid`

This Lean 3 fork of the Liquid Tensor Experiment identifies `src/solid/` as its
project-specific layer. Current `Mathlib/Condensed/Solid.lean` defines
`profiniteSolid`, solidification, and `CondensedMod.IsSolid`, but its module
documentation still records open solidity results and a limitation for general
rings.

Next gate: perform a semantic diff of the Lean 3 `src/solid/` declarations
against the current module. Do not infer correspondence from shared names, and
do not import the inherited Liquid Tensor infrastructure wholesale.

### `b-mehta/topos`

This Lean 3 project covers cartesian and locally cartesian closed categories,
toposes, Lawvere--Tierney topologies, and sheafification. Current Mathlib has
substantial category, site, Grothendieck-topology, and sheaf infrastructure, so
the relevant task is a theorem-by-theorem overlap audit rather than a source
tree port.

Next gate: inventory the source's named results and map them to current
declarations before selecting any unmatched theorem for reconstruction.

## Existing Lean 4 descendants and exclusions

- `ianklatzco/flypitch` contains a `flypitch4` development and validation
  records. Audit that existing descendant and its trusted boundary; do not
  begin a fresh Lean 3 port merely because the original `flypitch/flypitch`
  repository remains a Lean 3 project.
- `leanprover-community/sphere-eversion` states that it was ported from Lean 3
  to Lean 4 and currently has a Lake project. It may still be considered under
  the ordinary source-intake policy, but it is not a missing-port recovery
  task.

## Long-term cross-prover discovery

Flyspeck, a Cubical Agda computation of `pi_4(S^3)`, and the Rocq/Coq Four
Color Theorem are possible reformalization leads, not Lean ports. Keep them in
identity resolution until an exact maintained source, trusted boundary,
foundation gap, current Lean overlap, and realistic infrastructure cost have
been established. Do not infer absence of a Lean development from an
incomplete search.

## Lean 3 tooling boundary

The current `leanprover-community/mathport` documentation says that `mathport`
no longer works directly against modern Mathlib because current Mathlib removed
the port-era `#align` support. Its supported recovery route is to run
`mathlib4:v3-eol` with `mathport:v3-eol`, obtain a Lean 4 project on the old
baseline, and then upgrade it manually.

Use that route only when the generated code preserves useful structure. For a
reconstruction whose old foundations have been superseded, compare the cost and
semantic clarity of a current-API reimplementation rather than treating
`mathport` output as the required migration path.
