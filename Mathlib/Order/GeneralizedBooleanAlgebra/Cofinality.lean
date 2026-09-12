/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.Order.GeneralizedBooleanSubalgebra

/-!
# Countable separation and cofinality of generalized Boolean algebras

`GeneralizedBooleanAlgebra.CountableSeparationProperty` says that two countable, crosswise
disjoint families have a separator bounding the first family and disjoint from the second.
Countable suprema imply this property.

The main result is that every monotone sequence of generalized Boolean subalgebras exhausting
an algebra with countable separation reaches the whole algebra. The disjoint extraction uses
a bounded seed; countable separation supplies one even when the ambient algebra has no top.
The proof follows Koppelberg's diagonal argument, including the residual terms
`s j \ d (l j)` in the second separating family.

The extraction theorem also retains a strictly increasing subsequence of stages, with each
disjoint element belonging to the next stage but not the preceding one.

## References

* [Sabine Koppelberg, *Boolean algebras as unions of chains of subalgebras*][Koppelberg1977],
  Theorem 1, pp. 196–198.
-/

@[expose] public section

open Set

variable {B : Type*}

namespace GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra B]

variable (B) in
/-- The countable separation property of a generalized Boolean algebra: any two countable,
crosswise disjoint families have a common upper bound for the first family that is disjoint
from every member of the second family. -/
def CountableSeparationProperty : Prop :=
  ∀ ⦃M N : Set B⦄, M.Countable → N.Countable →
    (∀ m ∈ M, ∀ n ∈ N, Disjoint m n) →
    ∃ b : B, (∀ m ∈ M, m ≤ b) ∧ ∀ n ∈ N, Disjoint b n

/-- Countable suprema imply countable separation in a generalized Boolean algebra.
Only the supremum of the first separating family is needed. -/
theorem countableSeparationProperty_of_countable_isLUB
    (hcomplete : ∀ S : Set B, S.Countable → ∃ s, IsLUB S s) :
    CountableSeparationProperty B := by
  intro M N hM _ hdis
  obtain ⟨b, hb⟩ := hcomplete M hM
  refine ⟨b, fun m hm ↦ hb.1 hm, fun n hn ↦ ?_⟩
  exact disjoint_sdiff_self_left.mono_left
    (hb.2 fun m hm ↦ le_sdiff.mpr ⟨hb.1 hm, hdis m hm n hn⟩)

end GeneralizedBooleanAlgebra

namespace GeneralizedBooleanSubalgebra

variable [GeneralizedBooleanAlgebra B]

/-- If no stage of an exhaustive monotone chain contains all elements below a fixed bound,
one can pass to a strictly increasing subsequence and choose pairwise disjoint elements below
that bound belonging to each next stage but not the preceding stage. The bound need not belong
to every stage, and the ambient algebra need not have a top. -/
theorem exists_pairwise_disjoint_not_mem_subsequence
    (C : ℕ → GeneralizedBooleanSubalgebra B) (hC : Monotone C)
    (hcover : ∀ x, ∃ n, x ∈ C n) {a : B}
    (ha : ∀ n, ∃ x ≤ a, x ∉ C n) :
    ∃ j : ℕ → ℕ, StrictMono j ∧ ∃ d : ℕ → B, (∀ n, d n ≤ a) ∧
      (∀ n, d n ∈ C (j (n + 1))) ∧ (∀ n, d n ∉ C (j n)) ∧
      Pairwise (fun i j ↦ Disjoint (d i) (d j)) := by
  classical
  -- No stage contains the principal ideal below an unbounded support.
  let UnboundedWithin : B → Prop := fun b ↦ ∀ n, ∃ x ≤ b, x ∉ C n
  have hsplit {b c : B} (hb : UnboundedWithin b) :
      UnboundedWithin c ∨ UnboundedWithin (b \ c) := by
    by_contra h
    simp only [UnboundedWithin, not_or, not_forall, not_exists, not_and, not_not] at h
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := h
    obtain ⟨x, hxb, hx⟩ := hb (max i j)
    apply hx
    have hc := hC (le_max_left i j) (hi (x ⊓ c) inf_le_right)
    have hd := hC (le_max_right i j) (hj (x \ c) (sdiff_le_sdiff_right hxb))
    simpa only [sup_inf_sdiff] using (C (max i j)).sup_mem hc hd
  have hstep (n : ℕ) {b : B} (hbn : b ∈ C n) (hb : UnboundedWithin b) :
      ∃ k > n, ∃ c ≤ b, c ∈ C k ∧ UnboundedWithin c ∧ b \ c ∉ C n := by
    obtain ⟨c, hcb, hcn⟩ := hb n
    obtain ⟨j, hcj⟩ := hcover c
    let k := max (n + 1) j
    have hnk : n < k := (Nat.lt_succ_self n).trans_le (le_max_left _ _)
    have hbk : b ∈ C k := hC hnk.le hbn
    have hck : c ∈ C k := hC (le_max_right _ _) hcj
    rcases hsplit (c := c) hb with hl | hl
    · refine ⟨k, hnk, c, hcb, hck, hl, fun hd ↦ hcn ?_⟩
      simpa only [sdiff_sdiff_eq_self hcb] using (C n).sdiff_mem hbn hd
    · refine ⟨k, hnk, b \ c, sdiff_le, (C k).sdiff_mem hbk hck, hl, ?_⟩
      simpa only [sdiff_sdiff_eq_self hcb] using hcn
  let State := {p : ℕ × B // p.2 ∈ C p.1 ∧ UnboundedWithin p.2}
  have hnext (p : State) : ∃ q : State,
      p.1.1 < q.1.1 ∧ q.1.2 ≤ p.1.2 ∧ p.1.2 \ q.1.2 ∉ C p.1.1 := by
    obtain ⟨k, hk, c, hc, hck, hcu, hnew⟩ := hstep p.1.1 p.2.1 p.2.2
    exact ⟨⟨⟨k, c⟩, hck, hcu⟩, hk, hc, hnew⟩
  choose next hnext using hnext
  obtain ⟨N, hN⟩ := hcover a
  let p : ℕ → State := Nat.rec ⟨⟨N, a⟩, hN, ha⟩ (fun _ ↦ next)
  have hp (n : ℕ) :
      (p n).1.1 < (p (n + 1)).1.1 ∧ (p (n + 1)).1.2 ≤ (p n).1.2 ∧
      (p n).1.2 \ (p (n + 1)).1.2 ∉ C (p n).1.1 := hnext (p n)
  have hj : StrictMono (fun n ↦ (p n).1.1) :=
    strictMono_nat_of_lt_succ fun n ↦ (hp n).1
  have hanti : Antitone (fun n ↦ (p n).1.2) :=
    antitone_nat_of_succ_le fun n ↦ (hp n).2.1
  refine ⟨fun n ↦ (p n).1.1, hj, fun n ↦ (p n).1.2 \ (p (n + 1)).1.2,
    fun n ↦ sdiff_le.trans (hanti (Nat.zero_le n)), ?_, fun n ↦ (hp n).2.2, ?_⟩
  · exact fun n ↦ (C _).sdiff_mem (hC (hp n).1.le (p n).2.1) (p (n + 1)).2.1
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact disjoint_sdiff_self_left.mono_right
      (sdiff_le.trans (hanti (Nat.succ_le_of_lt h)))
  · exact (disjoint_sdiff_self_left.mono_right
      (sdiff_le.trans (hanti (Nat.succ_le_of_lt h)))).symm

/-- Pairwise disjoint elements escaping their respective stages can be extracted below any
bound whose principal ideal is not contained in a stage of an exhaustive monotone chain. -/
theorem exists_pairwise_disjoint_not_mem
    (C : ℕ → GeneralizedBooleanSubalgebra B) (hC : Monotone C)
    (hcover : ∀ x, ∃ n, x ∈ C n) {a : B}
    (ha : ∀ n, ∃ x ≤ a, x ∉ C n) :
    ∃ d : ℕ → B, (∀ n, d n ≤ a) ∧
      Pairwise (fun i j ↦ Disjoint (d i) (d j)) ∧ ∀ n, d n ∉ C n := by
  obtain ⟨j, hj, d, hda, _, hnot, hd⟩ :=
    exists_pairwise_disjoint_not_mem_subsequence C hC hcover ha
  exact ⟨d, hda, hd, fun n hn ↦ hnot n (hC (hj.id_le n) hn)⟩

/-- Countable separation forces every monotone exhaustive sequence of generalized Boolean
subalgebras to reach the whole algebra. This extends the obstruction in Koppelberg's
Theorem 1 to algebras without a greatest element. -/
theorem exists_eq_top_of_countableSeparationProperty
    (hsep : GeneralizedBooleanAlgebra.CountableSeparationProperty B)
    (C : ℕ → GeneralizedBooleanSubalgebra B) (hC : Monotone C)
    (hcover : ∀ b, ∃ n, b ∈ C n) :
    ∃ n, C n = ⊤ := by
  classical
  by_contra h
  push Not at h
  have hescape (n : ℕ) : ∃ b, b ∉ C n := by
    by_contra! hn
    exact h n (top_unique fun b _ ↦ hn b)
  choose escape hescape using hescape
  -- Countable separation against the empty family bounds all the escaping elements.
  obtain ⟨a, ha, _⟩ := hsep (countable_range escape) countable_empty
    (fun _ _ _ hn ↦ False.elim (notMem_empty _ hn))
  obtain ⟨d, _, hd, hnot⟩ := exists_pairwise_disjoint_not_mem C hC hcover
    (fun n ↦ ⟨escape n, ha _ ⟨n, rfl⟩, hescape n⟩)
  -- The fibers of `Nat.unpair` partition the natural numbers into infinite blocks.
  have hblock (k : ℕ) : ∃ s : B,
      (∀ i, (Nat.unpair i).1 = k → d i ≤ s) ∧
      ∀ i, (Nat.unpair i).1 ≠ k → Disjoint s (d i) := by
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
          · exact (ht j (l k) (by rwa [hl k])).symm.mono_right sdiff_le)
  have hinf (k : ℕ) : s k ⊓ x = d (l k) := by
    have hres : Disjoint x (s k \ d (l k)) := hy _ (Or.inr ⟨k, rfl⟩)
    apply le_antisymm
    · apply (disjoint_sdiff_iff_le inf_le_left (hsl k)).mp
      exact hres.mono_left inf_le_right
    · exact le_inf (hsl k) (hx _ ⟨k, rfl⟩)
  let k := rank x
  have hk : x ∈ C k := hrank x
  apply hnot (l k)
  rw [← hinf k]
  exact (C (l k)).inf_mem
    (hC (Nat.right_le_pair k (rank (s k))) (hrank (s k)))
    (hC (Nat.left_le_pair k (rank (s k))) hk)

/-- A monotone exhaustive sequence of generalized Boolean subalgebras is eventually top
when the ambient algebra has countable separation. -/
theorem exists_forall_eq_top_of_countableSeparationProperty
    (hsep : GeneralizedBooleanAlgebra.CountableSeparationProperty B)
    (C : ℕ → GeneralizedBooleanSubalgebra B) (hC : Monotone C)
    (hcover : ∀ b, ∃ n, b ∈ C n) :
    ∃ n, ∀ m, n ≤ m → C m = ⊤ := by
  obtain ⟨n, hn⟩ := exists_eq_top_of_countableSeparationProperty hsep C hC hcover
  exact ⟨n, fun m hnm ↦ top_unique (hn ▸ hC hnm)⟩

end GeneralizedBooleanSubalgebra
