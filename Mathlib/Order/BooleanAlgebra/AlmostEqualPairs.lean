/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Order.Atoms
public import Mathlib.Order.BooleanAlgebra.Cofinality

/-!
# Pairs of sets with finite symmetric difference

`BooleanSubalgebra.almostEqualPairs ι` is the Boolean subalgebra of `Set ι × Set ι`
whose two coordinates have finite symmetric difference. For `ι = ℕ`, its stages
consist of pairs whose coordinates agree from a given natural number onwards.
They form a strictly increasing exhaustive chain.

The application is the homomorphism-to-countable-cofinality implication of
Corollary 3.5 in [Stefan Geschke, *The coinitiality of a compact space*][Geschke2006],
pp. 246–247. This file does not establish the converse or the topological theorem.
-/

@[expose] public section

open Set
open scoped symmDiff

namespace BooleanSubalgebra

/-- The Boolean subalgebra of pairs of sets with finite symmetric difference. -/
def almostEqualPairs (ι : Type*) : BooleanSubalgebra (Set ι × Set ι) :=
  BooleanSubalgebra.ofBotSupCompl {p | (p.1 ∆ p.2).Finite} (by simp) (by
    intro p hp q hq
    exact (hp.union hq).subset union_symmDiff_union_subset) (by
    intro p hp
    change (p.1ᶜ ∆ p.2ᶜ).Finite
    rwa [compl_symmDiff_compl])

@[simp]
theorem mem_almostEqualPairs {ι : Type*} {p : Set ι × Set ι} :
    p ∈ almostEqualPairs ι ↔ (p.1 ∆ p.2).Finite := Iff.rfl

namespace AlmostEqualPairs

variable {ι : Type*}

/-- The atom with a singleton in its left coordinate and empty right coordinate. -/
def singletonLeft (i : ι) : almostEqualPairs ι :=
  ⟨({i}, ∅), by simp⟩

@[simp]
theorem coe_singletonLeft (i : ι) :
    (singletonLeft i : Set ι × Set ι) = ({i}, ∅) := rfl

theorem isAtom_singletonLeft (i : ι) : IsAtom (singletonLeft i) := by
  refine ⟨?_, fun p hp ↦ ?_⟩
  · intro h
    exact singleton_ne_empty i <|
      congrArg (fun p : almostEqualPairs ι ↦ (p : Set ι × Set ι).1) h
  · have hp₂ : p.val.2 = ∅ := eq_empty_of_subset_empty hp.le.2
    rcases (isAtom_singleton i).le_iff.mp hp.le.1 with hp₁ | hp₁
    · exact Subtype.ext (Prod.ext hp₁ hp₂)
    · exact (hp.ne (Subtype.ext (Prod.ext hp₁ hp₂))).elim

/-- The `k`-th stage consists of pairs whose coordinates agree at every `n ≥ k`. -/
def stage (k : ℕ) : BooleanSubalgebra (almostEqualPairs ℕ) :=
  BooleanSubalgebra.ofBotSupCompl
    {p | ∀ n, k ≤ n → (n ∈ p.val.1 ↔ n ∈ p.val.2)}
    (fun _ _ ↦ Iff.rfl)
    (fun _ hp _ hq n hn ↦ or_congr (hp n hn) (hq n hn))
    (fun _ hp n hn ↦ not_congr (hp n hn))

@[simp]
theorem mem_stage {k : ℕ} {p : almostEqualPairs ℕ} :
    p ∈ stage k ↔ ∀ n, k ≤ n → (n ∈ p.val.1 ↔ n ∈ p.val.2) := Iff.rfl

theorem mem_stage_iff_symmDiff_subset {k : ℕ} {p : almostEqualPairs ℕ} :
    p ∈ stage k ↔ p.val.1 ∆ p.val.2 ⊆ Iio k := by
  simp only [mem_stage, subset_def, mem_symmDiff, mem_Iio]
  constructor
  · intro hp n hn
    by_contra h
    have := hp n (Nat.le_of_not_gt h)
    tauto
  · intro hp n hn
    have : ¬(n ∈ p.val.1 ∧ n ∉ p.val.2 ∨ n ∈ p.val.2 ∧ n ∉ p.val.1) :=
      fun h ↦ (Nat.not_lt_of_ge hn) (hp n h)
    tauto

@[simp]
theorem singletonLeft_mem_stage_iff {i k : ℕ} :
    singletonLeft i ∈ stage k ↔ i < k := by
  rw [mem_stage_iff_symmDiff_subset]
  simp [singletonLeft, Set.symmDiff_def]

theorem monotone_stage : Monotone stage := by
  intro k l h p hp n hn
  exact hp n (h.trans hn)

theorem strictMono_stage : StrictMono stage := by
  intro k l h
  refine lt_of_le_not_ge (monotone_stage h.le) ?_
  intro h'
  have : singletonLeft k ∈ stage k := h' (singletonLeft_mem_stage_iff.mpr h)
  exact Nat.lt_irrefl k (singletonLeft_mem_stage_iff.mp this)

theorem stage_lt_top (k : ℕ) : stage k < ⊤ := by
  refine lt_top_iff_ne_top.mpr ?_
  intro h
  have : singletonLeft k ∈ stage k := h.symm ▸ mem_top
  exact Nat.lt_irrefl k (singletonLeft_mem_stage_iff.mp this)

theorem exists_mem_stage (p : almostEqualPairs ℕ) : ∃ k, p ∈ stage k := by
  obtain ⟨k, hk⟩ := p.prop.bddAbove
  refine ⟨k + 1, mem_stage_iff_symmDiff_subset.mpr ?_⟩
  intro n hn
  exact Nat.lt_succ_of_le (hk hn)

theorem iUnion_stage : (⋃ k, (stage k : Set (almostEqualPairs ℕ))) = univ := by
  ext p
  simp only [mem_iUnion, mem_univ, iff_true]
  exact exists_mem_stage p

/-- The algebra of almost equal pairs of subsets of `ℕ` has countable cofinality
by proper Boolean subalgebras. -/
theorem hasCountableCofinality : HasCountableCofinality (almostEqualPairs ℕ) :=
  ⟨stage, strictMono_stage, exists_mem_stage⟩

variable {A : Type*} [BooleanAlgebra A]

/-- Pulling the stages back preserves strict growth whenever the left singleton atoms
belong to the image. Surjectivity onto the algebra of almost equal pairs is unnecessary. -/
theorem strictMono_comap_stage (h : BoundedLatticeHom A (almostEqualPairs ℕ))
    (h_range : ∀ k, singletonLeft k ∈ range h) :
    StrictMono fun k ↦ (stage k).comap h := by
  intro k l hkl
  refine lt_of_le_not_ge (comap_mono (f := h) (monotone_stage hkl.le)) ?_
  intro hle
  obtain ⟨a, ha⟩ := h_range k
  have hal : a ∈ (stage l).comap h := by
    change h a ∈ stage l
    rw [ha]
    exact singletonLeft_mem_stage_iff.mpr hkl
  have hak : h a ∈ stage k := hle hal
  rw [ha] at hak
  exact Nat.lt_irrefl k (singletonLeft_mem_stage_iff.mp hak)

/-- Every element is captured by a pulled-back stage, for any bounded lattice homomorphism. -/
theorem exists_mem_comap_stage (h : BoundedLatticeHom A (almostEqualPairs ℕ)) (a : A) :
    ∃ k, a ∈ (stage k).comap h := exists_mem_stage (h a)

/-- A homomorphism whose image contains the left singleton atoms yields a strictly
increasing exhaustive chain by pulling back the stages. -/
theorem hasCountableCofinality_of_singletonLeft_mem_range
    (h : BoundedLatticeHom A (almostEqualPairs ℕ))
    (h_range : ∀ k, singletonLeft k ∈ range h) : HasCountableCofinality A :=
  ⟨fun k ↦ (stage k).comap h, strictMono_comap_stage h h_range, exists_mem_comap_stage h⟩

/-- The homomorphism-to-countable-cofinality implication of Geschke's Corollary 3.5:
if a Boolean homomorphism into the algebra of almost equal pairs has every atom in its
image, then its domain has countable cofinality by proper Boolean subalgebras.
This is only this implication of the corollary; no surjectivity is assumed. -/
theorem hasCountableCofinality_of_atoms_mem_range
    (h : BoundedLatticeHom A (almostEqualPairs ℕ))
    (h_atoms : ∀ p, IsAtom p → p ∈ range h) : HasCountableCofinality A :=
  hasCountableCofinality_of_singletonLeft_mem_range h
    (fun k ↦ h_atoms _ (isAtom_singletonLeft k))

end AlmostEqualPairs
end BooleanSubalgebra
