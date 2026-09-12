/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.MeasureTheory.SetAlgebra
public import Mathlib.Order.GeneralizedBooleanAlgebra.Cofinality

/-!
# Sigma-rings and increasing unions of rings

A sigma-ring is a ring of sets closed under countable unions. Unlike a sigma-algebra, it need
not contain the whole underlying space.

Overdijk, Simons, and Thiemann proved that an increasing sequence of rings whose ordinary union is
a sigma-ring must be eventually constant. The individual rings need not be sigma-rings. The proof
is the generalized Boolean countable-separation theorem; the set-ring and sigma-algebra results
are thin interfaces to that common engine.

## Main definitions and results

* `MeasureTheory.IsSetSigmaRing`: the property of being a sigma-ring of sets.
* `MeasureTheory.isSetRing_iUnion_of_monotone`: an increasing union of rings is a ring.
* `MeasureTheory.IsSetAlgebra.exists_pairwise_disjoint_not_mem_of_strictMono`: the common
  disjoint-block extraction for algebras of sets and sigma-algebras.
* `MeasureTheory.IsSetSigmaRing.exists_eq_iUnion`: one stage equals the union.
* `MeasureTheory.IsSetSigmaRing.eventually_constant_of_monotone`: the stabilization theorem.
* `MeasureTheory.not_isSetSigmaRing_iUnion_of_not_eventually_constant`: the negative formulation.

## References

* [D. A. Overdijk, F. H. Simons and J. G. F. Thiemann, *A comment on unions of rings*]
  [OverdijkSimonsThiemann1979], pp. 439--441.
-/

@[expose] public section

open Set

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)} {R : ℕ → Set (Set α)}

/-- A sigma-ring is a ring of sets closed under countable unions. It is not required to contain
the whole underlying space. -/
structure IsSetSigmaRing (C : Set (Set α)) : Prop extends isSetRing : IsSetRing C where
  iUnion_mem : ∀ ⦃s : ℕ → Set α⦄, (∀ n, s n ∈ C) → (⋃ n, s n) ∈ C

namespace IsSetSigmaRing

/-- A sigma-ring is closed under countable indexed unions. -/
theorem iUnion_mem_of_countable (hC : IsSetSigmaRing C) {ι : Type*} [Countable ι]
    {s : ι → Set α} (hs : ∀ i, s i ∈ C) : ⋃ i, s i ∈ C := by
  cases isEmpty_or_nonempty ι
  · simpa using hC.isSetRing.empty_mem
  · obtain ⟨f, hf⟩ := exists_surjective_nat ι
    rw [← iUnion_congr_of_surjective _ hf (fun _ ↦ rfl)]
    exact hC.iUnion_mem fun n ↦ hs (f n)

/-- A sigma-ring is closed under unions of countable families. -/
theorem sUnion_mem (hC : IsSetSigmaRing C) {S : Set (Set α)}
    (hS : S.Countable) (hSC : S ⊆ C) : ⋃₀ S ∈ C := by
  let _ := hS.to_subtype
  rw [sUnion_eq_iUnion]
  exact hC.iUnion_mem_of_countable fun s : S ↦ hSC s.property

end IsSetSigmaRing

end MeasureTheory

namespace IsSigmaAlgebra

variable {α : Type*} {C : Set (Set α)}

/-- Every sigma-algebra is a sigma-ring. -/
theorem isSetSigmaRing (hC : IsSigmaAlgebra C) : MeasureTheory.IsSetSigmaRing C where
  isSetRing := hC.isSetAlgebra.isSetRing
  iUnion_mem := by
    intro s hs
    exact hC.iUnion_mem_nat s hs

end IsSigmaAlgebra

namespace SigmaAlgebra

variable {α : Type*}

/-- The measurable sets of a sigma-algebra form a sigma-ring. -/
theorem isSetSigmaRing (𝓐 : SigmaAlgebra α) :
    MeasureTheory.IsSetSigmaRing (𝓐 : Set (Set α)) :=
  𝓐.isSigmaAlgebra.isSetSigmaRing

end SigmaAlgebra


namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)} {R : ℕ → Set (Set α)}

/-- The ordinary union of an increasing sequence of rings of sets is again a ring of sets. -/
theorem isSetRing_iUnion_of_monotone (hR : ∀ n, IsSetRing (R n)) (hm : Monotone R) :
    IsSetRing (⋃ n, R n) where
  empty_mem := mem_iUnion.mpr ⟨0, (hR 0).empty_mem⟩
  union_mem := by
    intro s t hs ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    obtain ⟨j, hj⟩ := mem_iUnion.mp ht
    exact mem_iUnion.mpr ⟨max i j,
      (hR _).union_mem (hm (le_max_left i j) hi) (hm (le_max_right i j) hj)⟩
  sdiff_mem := by
    intro s t hs ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    obtain ⟨j, hj⟩ := mem_iUnion.mp ht
    exact mem_iUnion.mpr ⟨max i j,
      (hR _).sdiff_mem (hm (le_max_left i j) hi) (hm (le_max_right i j) hj)⟩

namespace IsSetSigmaRing

/-- Every countable family in the generalized Boolean algebra carried by a sigma-ring has a
least upper bound, represented by its union. -/
theorem exists_isLUB_of_countable (hC : IsSetSigmaRing C)
    (S : Set hC.isSetRing.toGeneralizedBooleanSubalgebra) (hS : S.Countable) :
    ∃ s, IsLUB S s := by
  let T : Set (Set α) := Subtype.val '' S
  have hT : T.Countable := hS.image _
  have hTC : T ⊆ C := by
    rintro _ ⟨s, _, rfl⟩
    exact s.property
  let s : hC.isSetRing.toGeneralizedBooleanSubalgebra :=
    ⟨⋃₀ T, hC.sUnion_mem hT hTC⟩
  refine ⟨s, ?_, ?_⟩
  · intro t ht
    exact subset_sUnion_of_mem ⟨t, ht, rfl⟩
  · intro t ht x hx
    obtain ⟨u, hu, hxu⟩ := mem_sUnion.mp hx
    obtain ⟨u, huS, rfl⟩ := hu
    exact ht huS hxu

/-- The generalized Boolean algebra carried by a sigma-ring has the countable separation
property. -/
theorem countableSeparationProperty (hC : IsSetSigmaRing C) :
    GeneralizedBooleanAlgebra.CountableSeparationProperty
      hC.isSetRing.toGeneralizedBooleanSubalgebra :=
  GeneralizedBooleanAlgebra.countableSeparationProperty_of_countable_isLUB
    hC.exists_isLUB_of_countable

end IsSetSigmaRing

namespace IsSetAlgebra

/-- A strictly increasing sequence of algebras of sets admits pairwise disjoint new sets after
passing to a strictly increasing subsequence. This is the common finite-Boolean extraction used
by the sigma-algebra specialization. -/
theorem exists_pairwise_disjoint_not_mem_of_strictMono
    {A : ℕ → Set (Set α)} (hA : ∀ n, IsSetAlgebra (A n)) (hm : StrictMono A) :
    ∃ j : ℕ → ℕ, StrictMono j ∧ ∃ f : ℕ → Set α,
      (∀ n, f n ∈ A (j (n + 1))) ∧ (∀ n, f n ∉ A (j n)) ∧
      Pairwise (fun i j ↦ Disjoint (f i) (f j)) := by
  let hU : IsSetRing (⋃ n, A n) :=
    isSetRing_iUnion_of_monotone (fun n ↦ (hA n).isSetRing) hm.monotone
  let U := hU.toGeneralizedBooleanSubalgebra
  let D (n : ℕ) := (hA n).isSetRing.toGeneralizedBooleanSubalgebra.comapSubtype U
  have hD : Monotone D := fun i j hij ↦
    GeneralizedBooleanSubalgebra.comapSubtype_mono U (fun _ h ↦ hm.monotone hij h)
  have hcover : ∀ s : U, ∃ n, s ∈ D n := by
    intro s
    obtain ⟨n, hn⟩ := mem_iUnion.mp s.property
    exact ⟨n, hn⟩
  let a : U := ⟨univ, mem_iUnion.mpr ⟨0, (hA 0).univ_mem⟩⟩
  have ha : ∀ n, ∃ s ≤ a, s ∉ D n := by
    intro n
    have hnot : ¬A (n + 1) ⊆ A n := not_le_of_gt (hm (Nat.lt_succ_self n))
    change ¬∀ s, s ∈ A (n + 1) → s ∈ A n at hnot
    push Not at hnot
    obtain ⟨s, hs, hsn⟩ := hnot
    exact ⟨⟨s, mem_iUnion.mpr ⟨n + 1, hs⟩⟩, subset_univ _, hsn⟩
  obtain ⟨j, hj, d, _, hmem, hnot, hd⟩ :=
    GeneralizedBooleanSubalgebra.exists_pairwise_disjoint_not_mem_subsequence
      D hD hcover ha
  refine ⟨j, hj, fun n ↦ d n, fun n ↦ hmem n, fun n ↦ hnot n, ?_⟩
  exact fun _ _ hij ↦ GeneralizedBooleanSubalgebra.disjoint_coe.mpr (hd hij)

end IsSetAlgebra

/-- If the ordinary union of an increasing sequence of rings is a sigma-ring, then one of the
rings already equals the union. The individual rings need not be sigma-rings. This result was
proved by Overdijk, Simons, and Thiemann. -/
theorem IsSetSigmaRing.exists_eq_iUnion (hU : IsSetSigmaRing (⋃ n, R n))
    (hR : ∀ n, IsSetRing (R n)) (hm : Monotone R) : ∃ N, R N = ⋃ n, R n := by
  let U := hU.isSetRing.toGeneralizedBooleanSubalgebra
  let D (n : ℕ) := (hR n).toGeneralizedBooleanSubalgebra.comapSubtype U
  have hD : Monotone D := fun i j hij ↦
    GeneralizedBooleanSubalgebra.comapSubtype_mono U (fun _ h ↦ hm hij h)
  have hcover : ∀ s : U, ∃ n, s ∈ D n := by
    intro s
    obtain ⟨n, hn⟩ := mem_iUnion.mp s.property
    exact ⟨n, hn⟩
  obtain ⟨N, hN⟩ :=
    GeneralizedBooleanSubalgebra.exists_eq_top_of_countableSeparationProperty
      hU.countableSeparationProperty D hD hcover
  refine ⟨N, Subset.antisymm (subset_iUnion R N) ?_⟩
  intro s hs
  let t : U := ⟨s, hs⟩
  have : t ∈ D N := by rw [hN]; exact GeneralizedBooleanSubalgebra.mem_top
  exact this

/-- An increasing sequence of rings whose ordinary union is a sigma-ring is eventually constant.
This is the stabilization formulation of the preceding result. -/
theorem IsSetSigmaRing.eventually_constant_of_monotone (hU : IsSetSigmaRing (⋃ n, R n))
    (hR : ∀ n, IsSetRing (R n)) (hm : Monotone R) :
    ∃ N, ∀ n ≥ N, R n = R N := by
  obtain ⟨N, hN⟩ := hU.exists_eq_iUnion hR hm
  refine ⟨N, fun n hn ↦ Subset.antisymm ?_ (hm hn)⟩
  rw [hN]
  exact subset_iUnion R n

/-- The ordinary union of a non-eventually-constant increasing sequence of rings is not a
sigma-ring. The stages are arbitrary rings. -/
theorem not_isSetSigmaRing_iUnion_of_not_eventually_constant (hR : ∀ n, IsSetRing (R n))
    (hm : Monotone R) (hnot : ¬ ∃ N, ∀ n ≥ N, R n = R N) :
    ¬ IsSetSigmaRing (⋃ n, R n) :=
  fun hU ↦ hnot (hU.eventually_constant_of_monotone hR hm)

end MeasureTheory
