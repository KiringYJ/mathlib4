/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.MeasureTheory.SetRing
public import Mathlib.MeasureTheory.SigmaAlgebra.Constructions

/-!
# Increasing unions of sigma-algebras

Broughton and Huff proved that the ordinary union of a strictly increasing sequence of
sigma-algebras is not a sigma-algebra. The ordinary union of their collections of measurable
sets must be distinguished from the lattice supremum `⨆ n, 𝓐 n`, which is always a sigma-algebra.

The disjoint extraction and countable-chain obstruction are proved at the generalized Boolean
subalgebra level. This file retains the natural sigma-algebra statements as thin specializations.

For comparison, `mem_iSup_iff_of_countablyDirected` proves that the ordinary union does
agree with the supremum when every countable subfamily has an upper bound within the family.

## Main results

* `exists_pairwise_disjoint_not_mem_of_strictMono`: the disjoint-block lemma.
* `exists_mem_iSup_not_mem_of_strictMono`: the strong supremum witness.
* `not_isSigmaAlgebra_iUnion_of_strictMono`: the ordinary-union non-closure result proved by
  Broughton and Huff.

## References

* [Allen Broughton and Barthel W. Huff, *A Comment on Unions of Sigma-Fields*]
  [BroughtonHuff1977]
-/

@[expose] public section

open Set
open scoped MeasureTheory

namespace SigmaAlgebra

variable {α : Type*} {𝓐 : ℕ → SigmaAlgebra α}

/-- If every countable subfamily of a family of sigma-algebras has an upper bound in the family,
then a set is measurable in their supremum exactly when it is measurable in one member of the
family. Thus, in this situation, the lattice supremum agrees with the ordinary union of the
collections of measurable sets. -/
theorem mem_iSup_iff_of_countablyDirected {ι : Type*}
    {𝓐 : ι → SigmaAlgebra α}
    (hm : ∀ u : Set ι, u.Countable → ∃ i, ∀ j ∈ u, 𝓐 j ≤ 𝓐 i) {s : Set α} :
    s ∈ ⨆ i, 𝓐 i ↔ ∃ i, s ∈ 𝓐 i := by
  classical
  constructor
  · rw [iSup_eq_generateFrom]
    intro hs
    change GenerateMeasurable (⋃ i, (𝓐 i : Set (Set α))) s at hs
    induction hs with
    | basic s hs => exact mem_iUnion.mp hs
    | empty =>
        obtain ⟨i, -⟩ := hm ∅ countable_empty
        exact ⟨i, (𝓐 i).empty_mem⟩
    | compl s _ hs =>
        obtain ⟨i, hi⟩ := hs
        exact ⟨i, (𝓐 i).compl_mem hi⟩
    | iUnion s _ hs =>
        choose i hi using hs
        obtain ⟨j, hj⟩ := hm (range i) (countable_range i)
        exact ⟨j, (𝓐 j).iUnion_mem fun n ↦ hj (i n) ⟨n, rfl⟩ (hi n)⟩
  · rintro ⟨i, hi⟩
    exact (le_iSup 𝓐 i) hi

/-- A strictly increasing sequence of sigma-algebras admits disjoint new measurable sets after
passing to a strictly increasing subsequence. The extraction is inherited from the generalized
Boolean subalgebra theorem through the algebra-of-sets interface. -/
theorem exists_pairwise_disjoint_not_mem_of_strictMono (hm : StrictMono 𝓐) :
    ∃ j : ℕ → ℕ, StrictMono j ∧ ∃ f : ℕ → Set α,
      (∀ n, f n ∈ 𝓐 (j (n + 1))) ∧
      (∀ n, f n ∉ 𝓐 (j n)) ∧
      Pairwise (fun i j ↦ Disjoint (f i) (f j)) := by
  have hm' : StrictMono (fun n ↦ (𝓐 n : Set (Set α))) :=
    fun _ _ h ↦ SetLike.coe_ssubset_coe.mpr (hm h)
  exact MeasureTheory.IsSetAlgebra.exists_pairwise_disjoint_not_mem_of_strictMono
    (fun n ↦ (𝓐 n).isSetAlgebra) hm'

private theorem false_of_isSetSigmaRing_iUnion_of_strictMono (hm : StrictMono 𝓐)
    (hU : MeasureTheory.IsSetSigmaRing (⋃ n, (𝓐 n : Set (Set α)))) : False := by
  have hm' : StrictMono (fun n ↦ (𝓐 n : Set (Set α))) :=
    fun _ _ h ↦ SetLike.coe_ssubset_coe.mpr (hm h)
  obtain ⟨N, hN⟩ := hU.exists_eq_iUnion
    (fun n ↦ (𝓐 n).isSetAlgebra.isSetRing) hm'.monotone
  apply (hm (Nat.lt_succ_self N)).2
  intro s hs
  have hu : s ∈ ⋃ n, (𝓐 n : Set (Set α)) := mem_iUnion.mpr ⟨N + 1, hs⟩
  rwa [← hN] at hu

/-- A strengthening of the ordinary-union result proved by Broughton and Huff: the supremum of a
strictly increasing sequence of sigma-algebras contains a measurable set that belongs to none of
the sigma-algebras in the sequence. -/
theorem exists_mem_iSup_not_mem_of_strictMono (hm : StrictMono 𝓐) :
    ∃ s, s ∈ ⨆ n, 𝓐 n ∧ ∀ n, s ∉ 𝓐 n := by
  by_contra! h
  apply false_of_isSetSigmaRing_iUnion_of_strictMono hm
  have heq : (⋃ n, (𝓐 n : Set (Set α))) =
      ((⨆ n, 𝓐 n : SigmaAlgebra α) : Set (Set α)) := by
    ext s
    simp only [mem_iUnion]
    exact ⟨fun ⟨n, hn⟩ ↦ (le_iSup 𝓐 n) hn, h s⟩
  rw [heq]
  exact (⨆ n, 𝓐 n).isSetSigmaRing

/-- The ordinary union of the collections of measurable sets in a strictly increasing sequence of
sigma-algebras is not a sigma-algebra. This union differs from the lattice supremum. The result was
proved by Broughton and Huff. -/
theorem not_isSigmaAlgebra_iUnion_of_strictMono (hm : StrictMono 𝓐) :
    ¬ IsSigmaAlgebra (⋃ n, (𝓐 n : Set (Set α))) := by
  intro h
  exact false_of_isSetSigmaRing_iUnion_of_strictMono hm h.isSetSigmaRing

end SigmaAlgebra
