/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.MeasureTheory.SigmaAlgebra.Constructions
public import Mathlib.MeasureTheory.SetAlgebra

/-!
# Atoms and indistinguishability classes of sigma-algebras

An atom is a nonempty measurable set with no proper nonempty measurable subset. Separately, the
indistinguishability class of a point consists of the points having the same membership pattern on
all measurable sets. Such a class need not be measurable. This file relates the two notions and
characterizes indistinguishability classes in generated sigma-algebras.
-/

@[expose] public section

open Set

variable {α : Type*} {C : Set (Set α)} {x y : α}

namespace SigmaAlgebra

/-- A measurable atom of `m` is a nonempty member of `m` containing no proper nonempty member of
`m`. -/
def IsAtom (m : SigmaAlgebra α) (s : Set α) : Prop :=
  s ∈ m ∧ s.Nonempty ∧ ∀ ⦃t : Set α⦄, t ∈ m → t.Nonempty → t ⊆ s → t = s

lemma IsAtom.mem {m : SigmaAlgebra α} {s : Set α} (hs : m.IsAtom s) :
    s ∈ m :=
  hs.1

lemma IsAtom.nonempty {m : SigmaAlgebra α} {s : Set α} (hs : m.IsAtom s) : s.Nonempty :=
  hs.2.1

lemma IsAtom.eq_of_mem_nonempty_subset {m : SigmaAlgebra α} {s t : Set α}
    (hs : m.IsAtom s) (ht : t ∈ m) (htn : t.Nonempty) (hts : t ⊆ s) : t = s :=
  hs.2.2 ht htn hts

/-- A measurable indistinguishability class is an atom. -/
theorem isAtom_indistinguishabilityClass {m : SigmaAlgebra α} {x : α}
    (h : m.indistinguishabilityClass x ∈ m) :
    m.IsAtom (m.indistinguishabilityClass x) := by
  refine ⟨h, ⟨x, m.self_mem_indistinguishabilityClass x⟩, ?_⟩
  intro t ht ⟨y, hyt⟩ hts
  apply Set.Subset.antisymm hts
  rw [← m.indistinguishabilityClass_eq_of_mem (hts hyt)]
  exact m.indistinguishabilityClass_subset ht hyt

theorem isAtom_indistinguishabilityClass_iff {m : SigmaAlgebra α} {x : α} :
    m.IsAtom (m.indistinguishabilityClass x) ↔
      m.indistinguishabilityClass x ∈ m :=
  ⟨IsAtom.mem, isAtom_indistinguishabilityClass⟩

/-- An atom is the indistinguishability class of each of its points. -/
theorem IsAtom.eq_indistinguishabilityClass {m : SigmaAlgebra α} {s : Set α}
    (hs : m.IsAtom s) {x : α} (hx : x ∈ s) : s = m.indistinguishabilityClass x := by
  apply Set.Subset.antisymm
  · intro y hy t ht
    constructor
    · intro hxt
      have hst : s ∩ t = s := hs.eq_of_mem_nonempty_subset
        (m.inter_mem hs.mem ht) ⟨x, hx, hxt⟩ inter_subset_left
      exact (show y ∈ s ∩ t by simpa [hst] using hy).2
    · intro hyt
      have hst : s ∩ t = s := hs.eq_of_mem_nonempty_subset
        (m.inter_mem hs.mem ht) ⟨y, hy, hyt⟩ inter_subset_left
      exact (show x ∈ s ∩ t by simpa [hst] using hx).2
  · exact m.indistinguishabilityClass_subset hs.mem hx

/-- Two points are indistinguishable in a generated sigma-algebra exactly when no generator
distinguishes them. -/
theorem mem_indistinguishabilityClass_generateFrom_iff :
    y ∈ (generateFrom C).indistinguishabilityClass x ↔ ∀ s ∈ C, x ∈ s ↔ y ∈ s := by
  rw [mem_indistinguishabilityClass_iff, indistinguishable_iff_forall_mem]
  exact forall_generateFrom_mem_iff_mem_iff

/-- The indistinguishability class of a point in a generated sigma-algebra is its
generator-membership class. -/
theorem indistinguishabilityClass_generateFrom :
    (generateFrom C).indistinguishabilityClass x = {y | ∀ s ∈ C, x ∈ s ↔ y ∈ s} :=
  Set.ext fun _ ↦ mem_indistinguishabilityClass_generateFrom_iff

/-- If the generators are closed under complements, then the indistinguishability class of a point
is the intersection of the generators containing that point. -/
theorem indistinguishabilityClass_generateFrom_of_compl_mem
    (hC : ∀ ⦃s⦄, s ∈ C → sᶜ ∈ C) :
    (generateFrom C).indistinguishabilityClass x = ⋂ (s ∈ C) (_ : x ∈ s), s := by
  ext y
  rw [mem_indistinguishabilityClass_generateFrom_iff]
  simp only [mem_iInter]
  constructor
  · exact fun h s hs hxs ↦ (h s hs).mp hxs
  · intro h s hs
    constructor
    · exact h s hs
    · intro hys
      by_contra hxs
      exact (h sᶜ (hC hs) (by simpa using hxs)) hys

end SigmaAlgebra
