import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Broughton--Huff theorem on increasing unions of sigma-fields

Let `𝓐` be a strictly increasing sequence of sigma-fields on a fixed type. The ordinary union of
the collections of measurable sets in the sequence is not itself a sigma-field. Equivalently,
there is no measurable-space structure whose measurable sets are exactly the sets that are
measurable at some finite stage.

The lattice supremum `⨆ n, 𝓐 n` is always a measurable space, but it necessarily contains sets
that occur in none of the individual sigma-fields.

This is the main result of Allen Broughton and Barthel W. Huff, *A Comment on Unions of
Sigma-Fields*, The American Mathematical Monthly 84 (1977), no. 7, 553--554,
<https://doi.org/10.2307/2320022>.
-/

open scoped MeasureTheory

/-- A witness formulation of the Broughton--Huff theorem: the supremum contains a set that is
measurable in none of the sigma-fields in the sequence. -/
theorem BroughtonHuff.exists_measurableSet_iSup_not_measurableSet_of_strictMono
    {α : Type*} {𝓐 : ℕ → MeasurableSpace α} (hm : StrictMono 𝓐) :
    ∃ s, MeasurableSet[⨆ n, 𝓐 n] s ∧ ∀ n, ¬MeasurableSet[𝓐 n] s := by
  sorry

/-- **Broughton--Huff theorem.** The ordinary union of a strictly increasing sequence of
sigma-fields is not the collection of measurable sets of any measurable space. -/
theorem BroughtonHuff.not_exists_measurableSpace_iUnion_of_strictMono
    {α : Type*} {𝓐 : ℕ → MeasurableSpace α} (hm : StrictMono 𝓐) :
    ¬ ∃ 𝓐' : MeasurableSpace α,
      ∀ s, MeasurableSet[𝓐'] s ↔ ∃ n, MeasurableSet[𝓐 n] s := by
  sorry
