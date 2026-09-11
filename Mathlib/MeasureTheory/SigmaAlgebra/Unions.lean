/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.MeasureTheory.SigmaAlgebra.Constructions

/-!
# Increasing unions of sigma-algebras

Broughton and Huff proved that the ordinary union of a strictly increasing sequence of
sigma-algebras is not a sigma-algebra. The ordinary union of their collections of measurable
sets must be distinguished from the lattice supremum `⨆ n, m n`, which is always a sigma-algebra.

The proof first extracts pairwise disjoint sets that become measurable along a strictly
increasing subsequence. Passing to the countable set of blocks then reduces the obstruction
to a diagonal argument with indistinguishability classes.

For comparison, `mem_iSup_iff_of_countablyDirected` proves that the ordinary union does
agree with the supremum when every countable subfamily has an upper bound within the family.

## Main results

* `exists_pairwise_disjoint_not_mem_of_strictMono`: the disjoint-block lemma.
* `exists_mem_iSup_not_mem_of_strictMono`: the strong supremum witness.
* `not_isSigmaAlgebra_iUnion_of_strictMono`: the Broughton--Huff theorem for the ordinary union.

## References

* [Allen Broughton and Barthel W. Huff, *A Comment on Unions of Sigma-Fields*]
  [BroughtonHuff1977]
-/

@[expose] public section

open Set
open scoped MeasureTheory

namespace SigmaAlgebra

variable {α : Type*} {m : ℕ → SigmaAlgebra α}

/-- If every countable subfamily of a family of sigma-algebras has an upper bound in the family,
then a set is measurable in their supremum exactly when it is measurable in one member of the
family. Thus, in this situation, the lattice supremum agrees with the ordinary union of the
collections of measurable sets. -/
theorem mem_iSup_iff_of_countablyDirected {ι : Type*}
    {m : ι → SigmaAlgebra α}
    (hm : ∀ u : Set ι, u.Countable → ∃ i, ∀ j ∈ u, m j ≤ m i) {s : Set α} :
    s ∈ ⨆ i, m i ↔ ∃ i, s ∈ m i := by
  classical
  constructor
  · rw [iSup_eq_generateFrom]
    intro hs
    change GenerateMeasurable (⋃ i, (m i : Set (Set α))) s at hs
    induction hs with
    | basic s hs => exact mem_iUnion.mp hs
    | empty =>
        obtain ⟨i, -⟩ := hm ∅ countable_empty
        exact ⟨i, (m i).empty_mem⟩
    | compl s _ hs =>
        obtain ⟨i, hi⟩ := hs
        exact ⟨i, (m i).compl_mem hi⟩
    | iUnion s _ hs =>
        choose i hi using hs
        obtain ⟨j, hj⟩ := hm (range i) (countable_range i)
        exact ⟨j, (m j).iUnion_mem fun n ↦ hj (i n) ⟨n, rfl⟩ (hi n)⟩
  · rintro ⟨i, hi⟩
    exact (le_iSup m i) hi

private def UnboundedWithin (m : ℕ → SigmaAlgebra α) (c : Set α) : Prop :=
  ∀ n, ∃ s ⊆ c, (∃ k, MeasurableSet[m k] s) ∧ ¬ MeasurableSet[m n] s

private lemma unbounded_split (hm : Monotone m) {c a : Set α}
    (hc : UnboundedWithin m c) (ha : ∃ k, MeasurableSet[m k] a) :
    UnboundedWithin m a ∨ UnboundedWithin m (c \ a) := by
  classical
  by_contra! h
  rcases h with ⟨h₁, h₂⟩
  simp only [UnboundedWithin, not_forall, not_exists, not_and, not_not] at h₁ h₂
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  obtain ⟨s, hsc, ⟨k, hsk⟩, hs⟩ := hc (max n₁ n₂)
  obtain ⟨j, haj⟩ := ha
  have hsk' : MeasurableSet[m (max k j)] s := hm (le_max_left _ _) hsk
  have haj' : MeasurableSet[m (max k j)] a := hm (le_max_right _ _) haj
  have hi : MeasurableSet[m n₁] (s ∩ a) :=
    hn₁ _ inter_subset_right ⟨_, hsk'.inter haj'⟩
  have hd : MeasurableSet[m n₂] (s \ a) :=
    hn₂ _ (sdiff_subset_sdiff_left hsc) ⟨_, hsk'.diff haj'⟩
  apply hs
  have heq : s = (s ∩ a) ∪ (s \ a) := by simp
  rw [heq]
  have hi' : MeasurableSet[m (max n₁ n₂)] (s ∩ a) := hm (le_max_left _ _) hi
  have hd' : MeasurableSet[m (max n₁ n₂)] (s \ a) := hm (le_max_right _ _) hd
  exact hi'.union hd'

private lemma exists_split (hm : Monotone m) {n : ℕ} {c : Set α}
    (hc : MeasurableSet[m n] c) (hu : UnboundedWithin m c) :
    ∃ k > n, ∃ d ⊆ c, MeasurableSet[m k] d ∧ UnboundedWithin m d ∧
      ¬ MeasurableSet[m n] (c \ d) := by
  classical
  obtain ⟨a, hac, ⟨j, haj⟩, han⟩ := hu n
  let k := max (n + 1) j
  have hnk : n < k := (Nat.lt_succ_self _).trans_le (le_max_left _ _)
  have hck : MeasurableSet[m k] c := hm hnk.le hc
  have hak : MeasurableSet[m k] a := hm (le_max_right _ _) haj
  have hcan : ¬ MeasurableSet[m n] (c \ a) := by
    intro h
    apply han
    have heq : c \ (c \ a) = a := Set.sdiff_sdiff_cancel_left hac
    rw [← heq]
    exact hc.diff h
  rcases unbounded_split hm hu ⟨j, haj⟩ with hu' | hu'
  · exact ⟨k, hnk, a, hac, hak, hu', hcan⟩
  · refine ⟨k, hnk, c \ a, sdiff_subset, hck.diff hak, hu', ?_⟩
    have heq : c \ (c \ a) = a := Set.sdiff_sdiff_cancel_left hac
    rwa [heq]

/-- A strictly increasing sequence of sigma-algebras admits disjoint new measurable sets after
passing to a strictly increasing subsequence. -/
theorem exists_pairwise_disjoint_not_mem_of_strictMono (hm : StrictMono m) :
    ∃ j : ℕ → ℕ, StrictMono j ∧ ∃ f : ℕ → Set α,
      (∀ n, f n ∈ m (j (n + 1))) ∧
      (∀ n, f n ∉ m (j n)) ∧
      Pairwise (fun i j ↦ Disjoint (f i) (f j)) := by
  classical
  have hstart : UnboundedWithin m univ := by
    intro n
    have hnot : ¬ m (n + 1) ≤ m n := not_le_of_gt (hm (Nat.lt_succ_self _))
    change ¬ (∀ s, MeasurableSet[m (n + 1)] s → MeasurableSet[m n] s) at hnot
    push Not at hnot
    obtain ⟨s, hs, hn⟩ := hnot
    exact ⟨s, subset_univ _, ⟨n + 1, hs⟩, hn⟩
  let State := {p : ℕ × Set α // MeasurableSet[m p.1] p.2 ∧ UnboundedWithin m p.2}
  have hnext (p : State) : ∃ q : State,
      p.1.1 < q.1.1 ∧ q.1.2 ⊆ p.1.2 ∧ ¬ MeasurableSet[m p.1.1] (p.1.2 \ q.1.2) := by
    obtain ⟨k, hk, d, hd, hdmeas, hdu, hnew⟩ := exists_split hm.monotone p.2.1 p.2.2
    exact ⟨⟨⟨k, d⟩, hdmeas, hdu⟩, hk, hd, hnew⟩
  choose next hnext using hnext
  let p : ℕ → State := Nat.rec ⟨⟨0, univ⟩, MeasurableSet.univ, hstart⟩ (fun _ ↦ next)
  have hp (n : ℕ) : p (n + 1) = next (p n) := rfl
  have hpstep (n : ℕ) :
      (p n).1.1 < (p (n + 1)).1.1 ∧ (p (n + 1)).1.2 ⊆ (p n).1.2 ∧
      ¬ MeasurableSet[m (p n).1.1] ((p n).1.2 \ (p (n + 1)).1.2) := by
    simpa only [hp] using hnext (p n)
  have hj : StrictMono (fun n ↦ (p n).1.1) := strictMono_nat_of_lt_succ fun n ↦ (hpstep n).1
  have hc : Antitone (fun n ↦ (p n).1.2) := antitone_nat_of_succ_le fun n ↦ (hpstep n).2.1
  refine ⟨fun n ↦ (p n).1.1, hj, fun n ↦ (p n).1.2 \ (p (n + 1)).1.2, ?_,
    fun n ↦ (hpstep n).2.2, ?_⟩
  · intro n
    have hc : MeasurableSet[m (p (n + 1)).1.1] (p n).1.2 :=
      hm.monotone (hj (Nat.lt_succ_self n)).le (p n).2.1
    exact hc.diff (p (n + 1)).2.1
  · have hdis {i j : ℕ} (h : i < j) :
        Disjoint ((p i).1.2 \ (p (i + 1)).1.2) ((p j).1.2 \ (p (j + 1)).1.2) := by
      apply Set.disjoint_left.2
      intro x hxi hxj
      exact hxi.2 (hc (Nat.succ_le_of_lt h) hxj.1)
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hdis h
    · exact (hdis h).symm

private theorem nat_singletons_obstruction {d : ℕ → SigmaAlgebra ℕ}
    (hd : Monotone d)
    (hyes : ∀ n, MeasurableSet[d (n + 1)] {n})
    (hno : ∀ n, ¬ MeasurableSet[d n] {n})
    (hcover : ∀ s : Set ℕ, ∃ n, MeasurableSet[d n] s) : False := by
  classical
  let b (n : ℕ) : Set ℕ := (d n).indistinguishabilityClass n
  have hbm (n : ℕ) : MeasurableSet[d n] (b n) :=
    SigmaAlgebra.indistinguishabilityClass_mem_of_countable n
  have hbself (n : ℕ) : n ∈ b n := (d n).self_mem_indistinguishabilityClass n
  have hnext (n : ℕ) : ∃ q > n, q ∈ b n := by
    have hex : ∃ q, q ∈ b n ∧ q ≠ n := by
      by_contra! h
      have heq : b n = {n} := by
        apply Subset.antisymm
        · intro q hq
          simpa using h q hq
        · exact singleton_subset_iff.2 (hbself n)
      exact hno n (heq ▸ hbm n)
    obtain ⟨q, hq, hqn⟩ := hex
    refine ⟨q, ?_, hq⟩
    by_contra hle
    have hlt : q < n := by omega
    have hqm : MeasurableSet[d n] {q} := hd (Nat.succ_le_of_lt hlt) (hyes q)
    have hn : n ∈ ({q}ᶜ : Set ℕ) := by simp; omega
    have hq' : q ∈ ({q}ᶜ : Set ℕ) :=
      (d n).indistinguishabilityClass_subset hqm.compl hn hq
    simp at hq'
  choose next hnext using hnext
  let a : ℕ → ℕ := Nat.rec 0 (fun _ ↦ next)
  have haste (n : ℕ) : a n < a (n + 1) ∧ a (n + 1) ∈ b (a n) := hnext (a n)
  have ha : StrictMono a := strictMono_nat_of_lt_succ fun n ↦ (haste n).1
  have hbound (n : ℕ) : n ≤ a n := by
    induction n with
    | zero => omega
    | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (haste n).1)
  obtain ⟨N, hN⟩ := hcover (range fun k ↦ a (2 * k))
  have hle : N ≤ a (2 * N) := by have := hbound (2 * N); omega
  have hmeas : MeasurableSet[d (a (2 * N))] (range fun k ↦ a (2 * k)) := hd hle hN
  have hodd : a (2 * N + 1) ∈ range (fun k ↦ a (2 * k)) :=
    (d (a (2 * N))).indistinguishabilityClass_subset hmeas ⟨N, rfl⟩
      (haste (2 * N)).2
  obtain ⟨k, hk⟩ := hodd
  change a (2 * k) = a (2 * N + 1) at hk
  have heq : 2 * k = 2 * N + 1 := ha.injective hk
  omega

private def blockUnion {ι : Type*} (f : ι → Set α) (s : Set ι) : Set α := ⋃ i ∈ s, f i

private lemma blockUnion_compl {ι : Type*} {f : ι → Set α}
    (hf : Pairwise (fun i j ↦ Disjoint (f i) (f j))) (s : Set ι) :
    blockUnion f sᶜ = (⋃ i, f i) \ blockUnion f s := by
  ext x
  simp only [blockUnion, mem_iUnion, exists_prop, mem_compl_iff, mem_sdiff]
  constructor
  · rintro ⟨i, hi, hxi⟩
    refine ⟨⟨i, hxi⟩, ?_⟩
    rintro ⟨j, hj, hxj⟩
    by_cases hij : i = j
    · exact hi (hij ▸ hj)
    · exact (Set.disjoint_left.1 (hf hij) hxi hxj)
  · rintro ⟨⟨i, hxi⟩, hx⟩
    exact ⟨i, fun hi ↦ hx ⟨i, hi, hxi⟩, hxi⟩

/-- The sigma-algebra on the indices for which the corresponding union of blocks is measurable.
The support must be measurable so that taking complements corresponds to relative complements. -/
@[instance_reducible]
private def blockSigmaAlgebra {ι : Type*} (f : ι → Set α)
    (hf : Pairwise (fun i j ↦ Disjoint (f i) (f j))) (m : SigmaAlgebra α)
    (hcover : MeasurableSet[m] (⋃ i, f i)) : SigmaAlgebra ι where
  carrier := {s | MeasurableSet[m] (blockUnion f s)}
  isSigmaAlgebra := {
    empty_mem := by simp [blockUnion]
    compl_mem := by
      intro s hs
      change MeasurableSet[m] (blockUnion f sᶜ)
      change MeasurableSet[m] (blockUnion f s) at hs
      rw [blockUnion_compl hf]
      exact hcover.diff hs
    iUnion_mem_nat := by
      intro s hs
      have heq : blockUnion f (⋃ n, s n) = ⋃ n, blockUnion f (s n) := by
        ext x
        simp only [blockUnion, mem_iUnion, exists_prop]
        aesop
      change MeasurableSet[m] (blockUnion f (⋃ n, s n))
      change ∀ n, MeasurableSet[m] (blockUnion f (s n)) at hs
      rw [heq]
      exact .iUnion hs }

private theorem false_of_mem_iff_exists_of_strictMono (hm : StrictMono m)
    (m' : SigmaAlgebra α)
    (hcover : ∀ s, s ∈ m' ↔ ∃ n, s ∈ m n) : False := by
  classical
  obtain ⟨j, hj, f, hfm, hfn, hf⟩ :=
    exists_pairwise_disjoint_not_mem_of_strictMono hm
  have hfm' (n : ℕ) : MeasurableSet[m'] (f n) := (hcover _).2 ⟨_, hfm n⟩
  obtain ⟨p, hp⟩ := (hcover _).1 (MeasurableSet.iUnion hfm')
  have hjle (n : ℕ) : n ≤ j n := by
    induction n with
    | zero => omega
    | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (hj (Nat.lt_succ_self n)))
  have hsupport : MeasurableSet[m (j p)] (⋃ i, f (p + i)) := by
    have hprefix : MeasurableSet[m (j p)] (⋃ i ∈ Finset.range p, f i) :=
      (Finset.range p).measurableSet_biUnion fun i hi ↦
        hm.monotone (hj.monotone (Nat.succ_le_of_lt (Finset.mem_range.1 hi))) (hfm i)
    have heq : (⋃ i, f (p + i)) = (⋃ i, f i) \ ⋃ i ∈ Finset.range p, f i := by
      ext x
      simp only [mem_iUnion, exists_prop, mem_sdiff, Finset.mem_range]
      constructor
      · rintro ⟨i, hxi⟩
        refine ⟨⟨p + i, hxi⟩, ?_⟩
        rintro ⟨k, hk, hxk⟩
        exact Set.disjoint_left.1 (hf (by omega)) hxi hxk
      · rintro ⟨⟨i, hxi⟩, hx⟩
        have hpi : p ≤ i := by
          by_contra h
          exact hx ⟨i, by omega, hxi⟩
        refine ⟨i - p, ?_⟩
        simpa [Nat.add_sub_of_le hpi] using hxi
    rw [heq]
    have hp' : MeasurableSet[m (j p)] (⋃ i, f i) := hm.monotone (hjle p) hp
    exact hp'.diff hprefix
  have htail : Pairwise (fun i k ↦ Disjoint (f (p + i)) (f (p + k))) :=
    fun _ _ hik ↦ hf (by omega)
  let d (n : ℕ) : SigmaAlgebra ℕ :=
    blockSigmaAlgebra (fun i ↦ f (p + i)) htail (m (j (p + n)))
      (hm.monotone (hj.monotone (Nat.le_add_right p n)) hsupport)
  apply nat_singletons_obstruction (d := d)
  · intro n k hnk s hs
    change MeasurableSet[m (j (p + n))] (blockUnion (fun i ↦ f (p + i)) s) at hs
    change MeasurableSet[m (j (p + k))] (blockUnion (fun i ↦ f (p + i)) s)
    exact hm.monotone (hj.monotone (Nat.add_le_add_left hnk p)) hs
  · intro n
    change blockUnion (fun i ↦ f (p + i)) {n} ∈ m (j (p + (n + 1)))
    simpa [blockUnion, Nat.add_assoc] using hfm (p + n)
  · intro n hn
    apply hfn (p + n)
    change {n} ∈ d n at hn
    change blockUnion (fun i ↦ f (p + i)) {n} ∈ m (j (p + n)) at hn
    simpa [blockUnion, Nat.add_assoc] using hn
  · intro s
    have hs : MeasurableSet[m'] (blockUnion (fun i ↦ f (p + i)) s) :=
      .biUnion (to_countable s) fun i _ ↦ hfm' (p + i)
    obtain ⟨n, hn⟩ := (hcover _).1 hs
    refine ⟨n, ?_⟩
    change MeasurableSet[m (j (p + n))] (blockUnion (fun i ↦ f (p + i)) s)
    apply hm.monotone _ hn
    have := hjle (p + n)
    omega

/-- A strengthening of the **Broughton--Huff theorem**: the supremum of a strictly increasing
sequence of sigma-algebras contains a measurable set that belongs to none of the sigma-algebras in
the sequence. -/
theorem exists_mem_iSup_not_mem_of_strictMono (hm : StrictMono m) :
    ∃ s, s ∈ ⨆ n, m n ∧ ∀ n, s ∉ m n := by
  classical
  by_contra! h
  apply false_of_mem_iff_exists_of_strictMono hm (⨆ n, m n)
  intro s
  exact ⟨h s, fun ⟨n, hn⟩ ↦ (le_iSup m n) hn⟩

/-- **Broughton--Huff theorem**, stated for the ordinary union of the collections of measurable
sets. This union differs from the lattice supremum of a strictly increasing sequence. -/
theorem not_isSigmaAlgebra_iUnion_of_strictMono (hm : StrictMono m) :
    ¬ IsSigmaAlgebra (⋃ n, (m n : Set (Set α))) := by
  intro h
  apply false_of_mem_iff_exists_of_strictMono hm h.toSigmaAlgebra
  intro s
  change s ∈ ⋃ n, (m n : Set (Set α)) ↔ ∃ n, s ∈ m n
  exact mem_iUnion

end SigmaAlgebra
