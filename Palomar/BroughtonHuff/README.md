# Broughton--Huff theorem

This Lean project formalizes the Broughton--Huff theorem: the ordinary union of a strictly
increasing sequence of sigma-fields is not a sigma-field.

The project is prepared as a selected project for the
[Palomar Registry](https://palomar-registry.org/):

- `Challenge.lean` is the small statement surface for mathematical audit.
- `Solution.lean` connects that statement to the proof.
- `BroughtonHuff/Basic.lean` contains the proof development.
- `comparator.json` records the declaration that Comparator must match.
- `formalization.yaml` records provenance, scope, fidelity, and review status.

The proof works with Mathlib's `MeasurableSpace` API and is independent of the personal-fork
`SigmaAlgebra` refactor in the repository's `dev` branch. It first constructs pairwise disjoint
sets that enter along a strictly increasing subsequence and then applies a diagonal argument on
the induced measurable spaces of block indices.

## Source

Allen Broughton and Barthel W. Huff, “A Comment on Unions of Sigma-Fields,” *The American
Mathematical Monthly* 84 (1977), no. 7, 553--554.
<https://doi.org/10.2307/2320022>

The Challenge statement was checked directly against the theorem on printed page 554. The paper
indexes the sequence from 1 and assumes every successive inclusion is proper; the Lean statement
indexes from 0 and expresses the equivalent condition as `StrictMono`. The Lean proof preserves
the article's disjoint-block and diagonal structure while packaging its smallest measurable sets
with Mathlib's `measurableAtom` API.

The repository-root `LICENSE` applies to this project.
