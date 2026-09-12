/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.Order.BooleanSubalgebra

/-!
# Countable separation and cofinality of Boolean algebras

`BooleanAlgebra.CountableSeparationProperty` says that two countable, crosswise disjoint
families can be separated by an element and its complement. Koppelberg calls this property
*almost sigma-completeness*.

`BooleanSubalgebra.HasCountableCofinality` means that a Boolean algebra is the union of a
strictly increasing sequence of Boolean subalgebras. This concerns exhaustion by proper
subalgebras, not order cofinality in the Boolean algebra (which already has a greatest element).

The main result is that countable separation prevents such an exhaustion. More generally,
every monotone sequence of subalgebras exhausting the algebra reaches the top subalgebra.
The proof follows Koppelberg's diagonal argument, including the residual terms
`s j \ d (l j)` in the second separating family.

## References

* [Sabine Koppelberg, *Boolean algebras as unions of chains of subalgebras*][Koppelberg1977],
  Theorem 1, pp. 196–198.
-/

@[expose] public section

open Set

variable {B : Type*} [BooleanAlgebra B]

namespace BooleanAlgebra

variable (B) in
/-- The countable separation property of a Boolean algebra: any two countable families
whose members are crosswise disjoint have a separator. Koppelberg calls this property
*almost sigma-completeness*. -/
def CountableSeparationProperty : Prop :=
  ∀ ⦃M N : Set B⦄, M.Countable → N.Countable →
    (∀ m ∈ M, ∀ n ∈ N, Disjoint m n) →
    ∃ b : B, (∀ m ∈ M, m ≤ b) ∧ ∀ n ∈ N, n ≤ bᶜ

/-- A Boolean algebra in which every countable set has a supremum has the countable
separation property. This isolates the exact completeness input used to obtain Koppelberg's
hypothesis; no arbitrary suprema are required. -/
theorem countableSeparationProperty_of_countable_isLUB
    (hcomplete : ∀ S : Set B, S.Countable → ∃ s, IsLUB S s) :
    CountableSeparationProperty B := by
  intro M N hM _ hdis
  obtain ⟨b, hb⟩ := hcomplete M hM
  refine ⟨b, fun m hm ↦ hb.1 hm, fun n hn ↦ ?_⟩
  have hbn : b ≤ nᶜ := hb.2 fun m hm ↦ (hdis m hm n hn).le_compl_right
  simpa using compl_le_compl hbn

end BooleanAlgebra

namespace CompleteBooleanAlgebra

/-- Every complete Boolean algebra has the countable separation property. -/
theorem countableSeparationProperty (B : Type*) [CompleteBooleanAlgebra B] :
    BooleanAlgebra.CountableSeparationProperty B :=
  BooleanAlgebra.countableSeparationProperty_of_countable_isLUB fun S _ ↦
    ⟨sSup S, isLUB_sSup S⟩

end CompleteBooleanAlgebra

namespace BooleanSubalgebra

variable (B) in
/-- A Boolean algebra has countable cofinality by subalgebras if a strictly increasing
sequence of Boolean subalgebras exhausts it. Strict increase implies that every stage is
proper. This is distinct from order cofinality in the underlying Boolean algebra. -/
def HasCountableCofinality : Prop :=
  ∃ C : ℕ → BooleanSubalgebra B, StrictMono C ∧ ∀ b, ∃ n, b ∈ C n

private theorem exists_pairwise_disjoint_not_mem
    (C : ℕ → BooleanSubalgebra B) (hC : Monotone C)
    (hcover : ∀ b, ∃ n, b ∈ C n) (hproper : ∀ n, C n ≠ ⊤) :
    ∃ d : ℕ → B, Pairwise (fun i j ↦ Disjoint (d i) (d j)) ∧ ∀ n, d n ∉ C n := by
  classical
  -- An element is large if no stage contains its whole principal ideal.
  let Large : B → Prop := fun b ↦ ∀ n, ∃ x, x ≤ b ∧ x ∉ C n
  have htop : Large ⊤ := by
    intro n
    by_contra h
    push Not at h
    exact hproper n (top_unique fun x _ ↦ h x le_top)
  have hsplit {b c : B} (hb : Large b) : Large c ∨ Large (b \ c) := by
    by_contra h
    simp only [Large, not_or, not_forall, not_exists, not_and, not_not] at h
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := h
    obtain ⟨x, hxb, hx⟩ := hb (max i j)
    apply hx
    have hc := hC (le_max_left i j) (hi (x ⊓ c) inf_le_right)
    have hd := hC (le_max_right i j) (hj (x \ c) (sdiff_le_sdiff_right hxb))
    simpa only [sup_inf_sdiff] using (C (max i j)).sup_mem hc hd
  have hstep (n : ℕ) (b : {b : B // Large b}) :
      ∃ c : {b : B // Large b}, (c : B) ≤ b ∧ (b : B) \ c ∉ C n := by
    obtain ⟨m, hbm⟩ := hcover b
    obtain ⟨c, hcb, hc⟩ := b.property (max n m)
    have hbn := hC (le_max_right n m) hbm
    rcases hsplit b.property with hl | hl
    · refine ⟨⟨c, hl⟩, hcb, ?_⟩
      intro hd
      apply hc
      simpa only [sdiff_sdiff_eq_self hcb] using
        (C (max n m)).sdiff_mem hbn (hC (le_max_left n m) hd)
    · refine ⟨⟨(b : B) \ c, hl⟩, sdiff_le, ?_⟩
      intro hd
      rw [sdiff_sdiff_eq_self hcb] at hd
      exact hc (hC (le_max_left n m) hd)
  choose next hnext using hstep
  let b : ℕ → {b : B // Large b} := fun n ↦
    Nat.rec ⟨⊤, htop⟩ (fun n b ↦ next n b) n
  have hb (n : ℕ) :
      (b (n + 1)).val ≤ (b n).val ∧ (b n).val \ (b (n + 1)).val ∉ C n := by
    exact hnext n (b n)
  have hanti : Antitone (fun n ↦ (b n).val) := by
    apply antitone_nat_of_succ_le
    intro n
    exact (hb n).1
  refine ⟨fun n ↦ (b n).val \ (b (n + 1)).val, ?_, fun n ↦ (hb n).2⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact disjoint_sdiff_self_left.mono_right
      (sdiff_le.trans (hanti (Nat.succ_le_of_lt h)))
  · exact (disjoint_sdiff_self_left.mono_right
      (sdiff_le.trans (hanti (Nat.succ_le_of_lt h)))).symm

/-- Countable separation forces every monotone exhaustive sequence of Boolean subalgebras
to reach the whole algebra. This is the obstruction proved in Koppelberg's Theorem 1. -/
theorem exists_eq_top_of_countableSeparationProperty
    (hsep : BooleanAlgebra.CountableSeparationProperty B)
    (C : ℕ → BooleanSubalgebra B) (hC : Monotone C) (hcover : ∀ b, ∃ n, b ∈ C n) :
    ∃ n, C n = ⊤ := by
  classical
  by_contra h
  push Not at h
  obtain ⟨d, hd, hnot⟩ := exists_pairwise_disjoint_not_mem C hC hcover h
  -- The fibers of `Nat.unpair` partition the natural numbers into infinite blocks.
  have hblock (k : ℕ) : ∃ s : B,
      (∀ i, (Nat.unpair i).1 = k → d i ≤ s) ∧
      ∀ i, (Nat.unpair i).1 ≠ k → d i ≤ sᶜ := by
    obtain ⟨s, hs, ht⟩ := hsep
      ((to_countable {i : ℕ | (Nat.unpair i).1 = k}).image d)
      ((to_countable {i : ℕ | (Nat.unpair i).1 ≠ k}).image d) (by
        rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
        exact hd (fun hij ↦ hj (hij ▸ hi)))
    exact ⟨s, fun i hi ↦ hs _ ⟨i, hi, rfl⟩, fun i hi ↦ ht _ ⟨i, hi, rfl⟩⟩
  choose s hs ht using hblock
  choose rank hrank using hcover
  let l : ℕ → ℕ := fun k ↦ Nat.pair k (rank (s k))
  have hl (k : ℕ) : (Nat.unpair (l k)).1 = k := by simp [l]
  have hsl (k : ℕ) : d (l k) ≤ s k := hs k (l k) (hl k)
  -- The residual terms ensure that intersecting the final separator with `s k`
  -- gives exactly the selected `d (l k)`.
  obtain ⟨x, hx, hy⟩ := hsep (countable_range (fun k ↦ d (l k)))
    (((to_countable (range l)ᶜ).image d).union
      (countable_range (fun j ↦ s j \ d (l j)))) (by
        rintro _ ⟨k, rfl⟩ _ (⟨i, hi, rfl⟩ | ⟨j, rfl⟩)
        · exact hd (fun hki ↦ hi ⟨k, hki⟩)
        · by_cases hkj : k = j
          · subst j
            exact disjoint_sdiff_self_right
          · exact (le_compl_iff_disjoint_right.mp
              (ht j (l k) (by rwa [hl k]))).mono_right sdiff_le)
  have hinf (k : ℕ) : s k ⊓ x = d (l k) := by
    have hres : s k \ d (l k) ≤ xᶜ := hy _ (Or.inr ⟨k, rfl⟩)
    apply le_antisymm
    · apply (disjoint_sdiff_iff_le inf_le_left (hsl k)).mp
      exact (le_compl_iff_disjoint_left.mp hres).mono_left inf_le_right
    · exact le_inf (hsl k) (hx _ ⟨k, rfl⟩)
  let k := rank x
  have hk : x ∈ C k := hrank x
  apply hnot (l k)
  rw [← hinf k]
  exact (C (l k)).inf_mem
    (hC (Nat.right_le_pair k (rank (s k))) (hrank (s k)))
    (hC (Nat.left_le_pair k (rank (s k))) hk)

/-- A monotone exhaustive sequence in a Boolean algebra with countable separation
is eventually the constant sequence of top subalgebras. -/
theorem exists_forall_eq_top_of_countableSeparationProperty
    (hsep : BooleanAlgebra.CountableSeparationProperty B)
    (C : ℕ → BooleanSubalgebra B) (hC : Monotone C) (hcover : ∀ b, ∃ n, b ∈ C n) :
    ∃ n, ∀ m, n ≤ m → C m = ⊤ := by
  obtain ⟨n, hn⟩ := exists_eq_top_of_countableSeparationProperty hsep C hC hcover
  exact ⟨n, fun m hnm ↦ top_unique (hn ▸ hC hnm)⟩

/-- A Boolean algebra with countable separation has no strictly increasing countable
exhaustion by Boolean subalgebras (Koppelberg, Theorem 1). -/
theorem not_hasCountableCofinality_of_countableSeparationProperty
    (hsep : BooleanAlgebra.CountableSeparationProperty B) : ¬ HasCountableCofinality B := by
  rintro ⟨C, hC, hcover⟩
  obtain ⟨n, hn⟩ := exists_eq_top_of_countableSeparationProperty hsep C hC.monotone hcover
  exact (hC (Nat.lt_succ_self n)).not_ge (hn ▸ le_top)

end BooleanSubalgebra
