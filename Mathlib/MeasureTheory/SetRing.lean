/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.MeasureTheory.SetSemiring

/-!
# Sigma-rings and increasing unions of rings

A sigma-ring is a ring of sets closed under countable unions. Unlike a sigma-algebra, it need
not contain the whole underlying space.

The Overdijk--Simons--Thiemann theorem states that an increasing sequence of rings whose ordinary
union is a sigma-ring must be eventually constant. The individual rings need not be sigma-rings.
The proof extracts disjoint sets escaping successive stages, partitions them into countably many
infinite rows, and takes a diagonal union.

## Main definitions and results

* `MeasureTheory.IsSetSigmaRing`: the property of being a sigma-ring of sets.
* `MeasureTheory.isSetRing_iUnion_of_monotone`: an increasing union of rings is a ring.
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

private def UnboundedWithin (R : ℕ → Set (Set α)) (c : Set α) : Prop :=
  ∀ n, ∃ s ⊆ c, (∃ k, s ∈ R k) ∧ s ∉ R n

private lemma unbounded_split (hR : ∀ n, IsSetRing (R n)) (hm : Monotone R)
    {c a : Set α} (hc : UnboundedWithin R c) (ha : ∃ k, a ∈ R k) :
    UnboundedWithin R a ∨ UnboundedWithin R (c \ a) := by
  classical
  by_contra! h
  rcases h with ⟨h₁, h₂⟩
  simp only [UnboundedWithin, not_forall, not_exists, not_and, not_not] at h₁ h₂
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  obtain ⟨s, hsc, ⟨k, hsk⟩, hs⟩ := hc (max n₁ n₂)
  obtain ⟨j, haj⟩ := ha
  have hsk' : s ∈ R (max k j) := hm (le_max_left _ _) hsk
  have haj' : a ∈ R (max k j) := hm (le_max_right _ _) haj
  have hi : s ∩ a ∈ R n₁ :=
    hn₁ _ inter_subset_right ⟨_, (hR _).inter_mem hsk' haj'⟩
  have hd : s \ a ∈ R n₂ :=
    hn₂ _ (sdiff_subset_sdiff_left hsc) ⟨_, (hR _).sdiff_mem hsk' haj'⟩
  apply hs
  have heq : s = (s ∩ a) ∪ (s \ a) := by simp
  rw [heq]
  exact (hR _).union_mem (hm (le_max_left _ _) hi) (hm (le_max_right _ _) hd)

private lemma exists_unbounded_split (hR : ∀ n, IsSetRing (R n)) (hm : Monotone R)
    {n : ℕ} {c : Set α} (hc : c ∈ R n) (hu : UnboundedWithin R c) :
    ∃ k > n, ∃ d ⊆ c, d ∈ R k ∧ UnboundedWithin R d ∧ c \ d ∉ R n := by
  classical
  obtain ⟨a, hac, ⟨j, haj⟩, han⟩ := hu n
  let k := max (n + 1) j
  have hnk : n < k := (Nat.lt_succ_self _).trans_le (le_max_left _ _)
  have hck : c ∈ R k := hm hnk.le hc
  have hak : a ∈ R k := hm (le_max_right _ _) haj
  have hcan : c \ a ∉ R n := by
    intro h
    apply han
    rw [← Set.sdiff_sdiff_cancel_left hac]
    exact (hR n).sdiff_mem hc h
  rcases unbounded_split hR hm hu ⟨j, haj⟩ with hu' | hu'
  · exact ⟨k, hnk, a, hac, hak, hu', hcan⟩
  · refine ⟨k, hnk, c \ a, sdiff_subset, (hR k).sdiff_mem hck hak, hu', ?_⟩
    rwa [Set.sdiff_sdiff_cancel_left hac]

private lemma exists_pairwise_disjoint_not_mem (hR : ∀ n, IsSetRing (R n))
    (hm : Monotone R) {N : ℕ} {c : Set α} (hc : c ∈ R N)
    (hu : UnboundedWithin R c) :
    ∃ f : ℕ → Set α, (∀ n, ∃ k, f n ∈ R k) ∧ (∀ n, f n ∉ R n) ∧
      Pairwise (fun i j ↦ Disjoint (f i) (f j)) := by
  classical
  let State := {p : ℕ × Set α // p.2 ∈ R p.1 ∧ UnboundedWithin R p.2}
  have hnext (p : State) : ∃ q : State,
      p.1.1 < q.1.1 ∧ q.1.2 ⊆ p.1.2 ∧ p.1.2 \ q.1.2 ∉ R p.1.1 := by
    obtain ⟨k, hk, d, hd, hdk, hdu, hnew⟩ := exists_unbounded_split hR hm p.2.1 p.2.2
    exact ⟨⟨⟨k, d⟩, hdk, hdu⟩, hk, hd, hnew⟩
  choose next hnext using hnext
  let p : ℕ → State := Nat.rec ⟨⟨N, c⟩, hc, hu⟩ (fun _ ↦ next)
  have hp (n : ℕ) : p (n + 1) = next (p n) := rfl
  have hpstep (n : ℕ) :
      (p n).1.1 < (p (n + 1)).1.1 ∧ (p (n + 1)).1.2 ⊆ (p n).1.2 ∧
      (p n).1.2 \ (p (n + 1)).1.2 ∉ R (p n).1.1 := by
    simpa only [hp] using hnext (p n)
  have hj : StrictMono (fun n ↦ (p n).1.1) :=
    strictMono_nat_of_lt_succ fun n ↦ (hpstep n).1
  have hjle (n : ℕ) : n ≤ (p n).1.1 := by
    induction n with
    | zero => omega
    | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (hpstep n).1)
  have hanti : Antitone (fun n ↦ (p n).1.2) :=
    antitone_nat_of_succ_le fun n ↦ (hpstep n).2.1
  refine ⟨fun n ↦ (p n).1.2 \ (p (n + 1)).1.2, ?_, ?_, ?_⟩
  · intro n
    exact ⟨_, (hR _).sdiff_mem (hm (hj (Nat.lt_succ_self n)).le (p n).2.1)
      (p (n + 1)).2.1⟩
  · intro n hn
    exact (hpstep n).2.2 (hm (hjle n) hn)
  · have hdis {i j : ℕ} (h : i < j) :
        Disjoint ((p i).1.2 \ (p (i + 1)).1.2) ((p j).1.2 \ (p (j + 1)).1.2) := by
      apply Set.disjoint_left.2
      intro x hxi hxj
      exact hxi.2 (hanti (Nat.succ_le_of_lt h) hxj.1)
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hdis h
    · exact (hdis h).symm

private theorem disjoint_diagonal_obstruction (hR : ∀ n, IsSetRing (R n))
    (hm : Monotone R) (hU : IsSetSigmaRing (⋃ n, R n)) {f : ℕ → Set α}
    (hfm : ∀ n, f n ∈ ⋃ k, R k) (hfn : ∀ n, f n ∉ R n)
    (hf : Pairwise (fun i j ↦ Disjoint (f i) (f j))) : False := by
  classical
  let row (p : ℕ) : Set α := ⋃ k, f (Nat.pair p k)
  have hrow (p : ℕ) : ∃ n, row p ∈ R n :=
    mem_iUnion.mp (hU.iUnion_mem fun k ↦ hfm (Nat.pair p k))
  choose n hn using hrow
  let m (p : ℕ) := Nat.pair p (max (n p) p)
  have hmle (p : ℕ) : max (n p) p ≤ m p := Nat.right_le_pair _ _
  obtain ⟨q, hq⟩ := mem_iUnion.mp (hU.iUnion_mem fun p ↦ hfm (m p))
  have heq : row q ∩ (⋃ p, f (m p)) = f (m q) := by
    apply Subset.antisymm
    · rintro x ⟨hxrow, hxdiag⟩
      obtain ⟨k, hk⟩ := mem_iUnion.mp hxrow
      obtain ⟨p, hp⟩ := mem_iUnion.mp hxdiag
      have heq : Nat.pair q k = m p := by
        by_contra hne
        exact Set.disjoint_left.mp (hf hne) hk hp
      have hqp : q = p := (Nat.pair_eq_pair.mp heq).1
      simpa [hqp] using hp
    · intro x hx
      exact ⟨mem_iUnion.mpr ⟨max (n q) q, hx⟩, mem_iUnion.mpr ⟨q, hx⟩⟩
  apply hfn (m q)
  rw [← heq]
  exact (hR _).inter_mem (hm ((le_max_left _ _).trans (hmle q)) (hn q))
    (hm ((le_max_right _ _).trans (hmle q)) hq)

/-- **Overdijk--Simons--Thiemann theorem**: if the ordinary union of an increasing sequence of
rings is a sigma-ring, then one of the rings already equals the union. The individual rings need
not be sigma-rings. -/
theorem IsSetSigmaRing.exists_eq_iUnion (hU : IsSetSigmaRing (⋃ n, R n))
    (hR : ∀ n, IsSetRing (R n)) (hm : Monotone R) : ∃ N, R N = ⋃ n, R n := by
  classical
  by_contra! hne
  have hescape (n : ℕ) : ∃ s, s ∈ (⋃ k, R k) ∧ s ∉ R n := by
    by_contra! h
    exact hne n (Subset.antisymm (subset_iUnion R n) h)
  choose s hs hn using hescape
  obtain ⟨N, hN⟩ := mem_iUnion.mp (hU.iUnion_mem hs)
  have hu : UnboundedWithin R (⋃ n, s n) :=
    fun n ↦ ⟨s n, subset_iUnion s n, mem_iUnion.mp (hs n), hn n⟩
  obtain ⟨f, hfm, hfn, hf⟩ := exists_pairwise_disjoint_not_mem hR hm hN hu
  exact disjoint_diagonal_obstruction hR hm hU (fun n ↦ mem_iUnion.mpr (hfm n)) hfn hf

/-- An increasing sequence of rings whose ordinary union is a sigma-ring is eventually constant.
This is the stabilization formulation of the Overdijk--Simons--Thiemann theorem. -/
theorem IsSetSigmaRing.eventually_constant_of_monotone (hU : IsSetSigmaRing (⋃ n, R n))
    (hR : ∀ n, IsSetRing (R n)) (hm : Monotone R) :
    ∃ N, ∀ n ≥ N, R n = R N := by
  obtain ⟨N, hN⟩ := hU.exists_eq_iUnion hR hm
  refine ⟨N, fun n hn ↦ Subset.antisymm ?_ (hm hn)⟩
  rw [hN]
  exact subset_iUnion R n

/-- The ordinary union of a non-eventually-constant increasing sequence of rings is not a
sigma-ring. The stages are arbitrary rings, as in the Overdijk--Simons--Thiemann theorem. -/
theorem not_isSetSigmaRing_iUnion_of_not_eventually_constant (hR : ∀ n, IsSetRing (R n))
    (hm : Monotone R) (hnot : ¬ ∃ N, ∀ n ≥ N, R n = R N) :
    ¬ IsSetSigmaRing (⋃ n, R n) :=
  fun hU ↦ hnot (hU.eventually_constant_of_monotone hR hm)

end MeasureTheory
