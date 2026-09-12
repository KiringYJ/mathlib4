/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/

import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Increasing unions of sigma-fields

Broughton and Huff proved that the ordinary union of a strictly increasing sequence of
sigma-fields is not a sigma-field. The ordinary union of their collections of measurable sets
must be distinguished from their lattice supremum, which is always a sigma-field.

The proof first extracts pairwise disjoint sets that become measurable along a strictly increasing
subsequence. Passing to the countable set of blocks then reduces the obstruction to a diagonal
argument with measurable atoms.

## Main results

* `BroughtonHuff.proof_exists_measurableSet_iSup_not_measurableSet_of_strictMono` gives a set in
  the supremum that is measurable in none of the sequence terms.
* `BroughtonHuff.proof_not_exists_measurableSpace_iUnion_of_strictMono` proves the
  Broughton--Huff theorem advertised in `Challenge.lean`.

## References

* Allen Broughton and Barthel W. Huff, *A Comment on Unions of Sigma-Fields*,
  The American Mathematical Monthly 84 (1977), no. 7, 553--554.
-/

open Set
open scoped MeasureTheory

namespace BroughtonHuff

variable {α : Type*} {𝓐 : ℕ → MeasurableSpace α}

/-- If every countable subfamily of a family of sigma-fields has an upper bound in the family,
then a set is measurable in their supremum exactly when it is measurable in one member. -/
theorem measurableSet_iSup_iff_of_countablyDirected {ι : Type*}
    {𝓐 : ι → MeasurableSpace α}
    (hm : ∀ u : Set ι, u.Countable → ∃ i, ∀ j ∈ u, 𝓐 j ≤ 𝓐 i) {s : Set α} :
    MeasurableSet[⨆ i, 𝓐 i] s ↔ ∃ i, MeasurableSet[𝓐 i] s := by
  classical
  constructor
  · rw [MeasurableSpace.measurableSpace_iSup_eq]
    intro hs
    change MeasurableSpace.GenerateMeasurable {s | ∃ i, MeasurableSet[𝓐 i] s} s at hs
    induction hs with
    | basic s hs => exact hs
    | empty =>
        obtain ⟨i, -⟩ := hm ∅ countable_empty
        exact ⟨i, @MeasurableSet.empty α (𝓐 i)⟩
    | compl s _ hs =>
        obtain ⟨i, hi⟩ := hs
        exact ⟨i, hi.compl⟩
    | iUnion s _ hs =>
        choose i hi using hs
        obtain ⟨j, hj⟩ := hm (range i) (countable_range i)
        exact ⟨j, MeasurableSet.iUnion fun n ↦ hj (i n) ⟨n, rfl⟩ _ (hi n)⟩
  · rintro ⟨i, hi⟩
    exact (le_iSup 𝓐 i) _ hi

private def UnboundedWithin (𝓐 : ℕ → MeasurableSpace α) (c : Set α) : Prop :=
  ∀ n, ∃ s ⊆ c, (∃ k, MeasurableSet[𝓐 k] s) ∧ ¬MeasurableSet[𝓐 n] s

private lemma unbounded_split (hm : Monotone 𝓐) {c a : Set α}
    (hc : UnboundedWithin 𝓐 c) (ha : ∃ k, MeasurableSet[𝓐 k] a) :
    UnboundedWithin 𝓐 a ∨ UnboundedWithin 𝓐 (c \ a) := by
  classical
  by_contra! h
  rcases h with ⟨h₁, h₂⟩
  simp only [UnboundedWithin, not_forall, not_exists, not_and, not_not] at h₁ h₂
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  obtain ⟨s, hsc, ⟨k, hsk⟩, hs⟩ := hc (max n₁ n₂)
  obtain ⟨j, haj⟩ := ha
  have hsk' : MeasurableSet[𝓐 (max k j)] s := hm (le_max_left _ _) _ hsk
  have haj' : MeasurableSet[𝓐 (max k j)] a := hm (le_max_right _ _) _ haj
  have hi : MeasurableSet[𝓐 n₁] (s ∩ a) :=
    hn₁ _ inter_subset_right ⟨_, hsk'.inter haj'⟩
  have hd : MeasurableSet[𝓐 n₂] (s \ a) :=
    hn₂ _ (sdiff_subset_sdiff_left hsc) ⟨_, hsk'.diff haj'⟩
  apply hs
  have heq : s = (s ∩ a) ∪ (s \ a) := by simp
  rw [heq]
  have hi' : MeasurableSet[𝓐 (max n₁ n₂)] (s ∩ a) := hm (le_max_left _ _) _ hi
  have hd' : MeasurableSet[𝓐 (max n₁ n₂)] (s \ a) := hm (le_max_right _ _) _ hd
  exact hi'.union hd'

private lemma exists_split (hm : Monotone 𝓐) {n : ℕ} {c : Set α}
    (hc : MeasurableSet[𝓐 n] c) (hu : UnboundedWithin 𝓐 c) :
    ∃ k > n, ∃ d ⊆ c, MeasurableSet[𝓐 k] d ∧ UnboundedWithin 𝓐 d ∧
      ¬MeasurableSet[𝓐 n] (c \ d) := by
  classical
  obtain ⟨a, hac, ⟨j, haj⟩, han⟩ := hu n
  let k := max (n + 1) j
  have hnk : n < k := (Nat.lt_succ_self _).trans_le (le_max_left _ _)
  have hck : MeasurableSet[𝓐 k] c := hm hnk.le _ hc
  have hak : MeasurableSet[𝓐 k] a := hm (le_max_right _ _) _ haj
  have hcan : ¬MeasurableSet[𝓐 n] (c \ a) := by
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

/-- A strictly increasing sequence of sigma-fields admits disjoint new measurable sets after
passing to a strictly increasing subsequence. -/
theorem exists_pairwise_disjoint_not_measurableSet_of_strictMono (hm : StrictMono 𝓐) :
    ∃ j : ℕ → ℕ, StrictMono j ∧ ∃ f : ℕ → Set α,
      (∀ n, MeasurableSet[𝓐 (j (n + 1))] (f n)) ∧
      (∀ n, ¬MeasurableSet[𝓐 (j n)] (f n)) ∧
      Pairwise (fun i j ↦ Disjoint (f i) (f j)) := by
  classical
  have hstart : UnboundedWithin 𝓐 univ := by
    intro n
    have hnot : ¬ 𝓐 (n + 1) ≤ 𝓐 n := not_le_of_gt (hm (Nat.lt_succ_self _))
    change ¬ (∀ s, MeasurableSet[𝓐 (n + 1)] s → MeasurableSet[𝓐 n] s) at hnot
    push Not at hnot
    obtain ⟨s, hs, hn⟩ := hnot
    exact ⟨s, subset_univ _, ⟨n + 1, hs⟩, hn⟩
  let State := {p : ℕ × Set α // MeasurableSet[𝓐 p.1] p.2 ∧ UnboundedWithin 𝓐 p.2}
  have hnext (p : State) : ∃ q : State,
      p.1.1 < q.1.1 ∧ q.1.2 ⊆ p.1.2 ∧ ¬MeasurableSet[𝓐 p.1.1] (p.1.2 \ q.1.2) := by
    obtain ⟨k, hk, d, hd, hdmeas, hdu, hnew⟩ := exists_split hm.monotone p.2.1 p.2.2
    exact ⟨⟨⟨k, d⟩, hdmeas, hdu⟩, hk, hd, hnew⟩
  choose next hnext using hnext
  let p : ℕ → State :=
    Nat.rec ⟨⟨0, univ⟩, @MeasurableSet.univ α (𝓐 0), hstart⟩ (fun _ ↦ next)
  have hp (n : ℕ) : p (n + 1) = next (p n) := rfl
  have hpstep (n : ℕ) :
      (p n).1.1 < (p (n + 1)).1.1 ∧ (p (n + 1)).1.2 ⊆ (p n).1.2 ∧
      ¬MeasurableSet[𝓐 (p n).1.1] ((p n).1.2 \ (p (n + 1)).1.2) := by
    simpa only [hp] using hnext (p n)
  have hj : StrictMono (fun n ↦ (p n).1.1) := strictMono_nat_of_lt_succ fun n ↦ (hpstep n).1
  have hc : Antitone (fun n ↦ (p n).1.2) := antitone_nat_of_succ_le fun n ↦ (hpstep n).2.1
  refine ⟨fun n ↦ (p n).1.1, hj, fun n ↦ (p n).1.2 \ (p (n + 1)).1.2, ?_,
    fun n ↦ (hpstep n).2.2, ?_⟩
  · intro n
    have hc : MeasurableSet[𝓐 (p (n + 1)).1.1] (p n).1.2 :=
      hm.monotone (hj (Nat.lt_succ_self n)).le _ (p n).2.1
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

private theorem nat_singletons_obstruction {d : ℕ → MeasurableSpace ℕ}
    (hd : Monotone d)
    (hyes : ∀ n, MeasurableSet[d (n + 1)] {n})
    (hno : ∀ n, ¬MeasurableSet[d n] {n})
    (hcover : ∀ s : Set ℕ, ∃ n, MeasurableSet[d n] s) : False := by
  classical
  let b (n : ℕ) : Set ℕ := @measurableAtom ℕ (d n) n
  have hbm (n : ℕ) : MeasurableSet[d n] (b n) := by
    change MeasurableSet[d n] (@measurableAtom ℕ (d n) n)
    exact @MeasurableSet.measurableAtom_of_countable ℕ (d n) _ n
  have hbself (n : ℕ) : n ∈ b n := by
    change n ∈ @measurableAtom ℕ (d n) n
    exact @mem_measurableAtom_self ℕ (d n) n
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
    have hqm : MeasurableSet[d n] {q} := hd (Nat.succ_le_of_lt hlt) _ (hyes q)
    have hn : n ∈ ({q}ᶜ : Set ℕ) := by simp; omega
    have hq' : q ∈ ({q}ᶜ : Set ℕ) := by
      change q ∈ @measurableAtom ℕ (d n) n at hq
      exact @mem_of_mem_measurableAtom ℕ (d n) n q hq _ hqm.compl hn
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
  have hmeas : MeasurableSet[d (a (2 * N))] (range fun k ↦ a (2 * k)) := hd hle _ hN
  have hodd : a (2 * N + 1) ∈ range (fun k ↦ a (2 * k)) := by
    have hatom := (haste (2 * N)).2
    change a (2 * N + 1) ∈ @measurableAtom ℕ (d (a (2 * N))) (a (2 * N)) at hatom
    exact @mem_of_mem_measurableAtom ℕ (d (a (2 * N))) (a (2 * N))
      (a (2 * N + 1)) hatom _ hmeas ⟨N, rfl⟩
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
    · exact Set.disjoint_left.1 (hf hij) hxi hxj
  · rintro ⟨⟨i, hxi⟩, hx⟩
    exact ⟨i, fun hi ↦ hx ⟨i, hi, hxi⟩, hxi⟩

/-- The measurable space on the indices for which the corresponding union of blocks is measurable.
The support must be measurable so that taking complements corresponds to relative complements. -/
@[implicit_reducible]
private def blockMeasurableSpace {ι : Type*} (f : ι → Set α)
    (hf : Pairwise (fun i j ↦ Disjoint (f i) (f j))) (𝓐 : MeasurableSpace α)
    (hcover : MeasurableSet[𝓐] (⋃ i, f i)) : MeasurableSpace ι where
  MeasurableSet' := fun s ↦ MeasurableSet[𝓐] (blockUnion f s)
  measurableSet_empty := by simp [blockUnion]
  measurableSet_compl := by
    intro s hs
    change MeasurableSet[𝓐] (blockUnion f s) at hs
    rw [blockUnion_compl hf]
    exact hcover.diff hs
  measurableSet_iUnion := by
    intro s hs
    have heq : blockUnion f (⋃ n, s n) = ⋃ n, blockUnion f (s n) := by
      ext x
      simp only [blockUnion, mem_iUnion, exists_prop]
      aesop
    change MeasurableSet[𝓐] (blockUnion f (⋃ n, s n))
    change ∀ n, MeasurableSet[𝓐] (blockUnion f (s n)) at hs
    rw [heq]
    exact MeasurableSet.iUnion hs

private theorem false_of_measurableSet_iff_exists_of_strictMono (hm : StrictMono 𝓐)
    (𝓐' : MeasurableSpace α)
    (hcover : ∀ s, MeasurableSet[𝓐'] s ↔ ∃ n, MeasurableSet[𝓐 n] s) : False := by
  classical
  obtain ⟨j, hj, f, hfm, hfn, hf⟩ :=
    exists_pairwise_disjoint_not_measurableSet_of_strictMono hm
  have hfm' (n : ℕ) : MeasurableSet[𝓐'] (f n) := (hcover _).2 ⟨_, hfm n⟩
  obtain ⟨p, hp⟩ := (hcover _).1 (MeasurableSet.iUnion hfm')
  have hjle (n : ℕ) : n ≤ j n := by
    induction n with
    | zero => omega
    | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (hj (Nat.lt_succ_self n)))
  have hsupport : MeasurableSet[𝓐 (j p)] (⋃ i, f (p + i)) := by
    have hprefix : MeasurableSet[𝓐 (j p)] (⋃ i ∈ Finset.range p, f i) :=
      (Finset.range p).measurableSet_biUnion fun i hi ↦
        hm.monotone (hj.monotone (Nat.succ_le_of_lt (Finset.mem_range.1 hi))) _ (hfm i)
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
    have hp' : MeasurableSet[𝓐 (j p)] (⋃ i, f i) := hm.monotone (hjle p) _ hp
    exact hp'.diff hprefix
  have htail : Pairwise (fun i k ↦ Disjoint (f (p + i)) (f (p + k))) :=
    fun _ _ hik ↦ hf (by omega)
  let d (n : ℕ) : MeasurableSpace ℕ :=
    blockMeasurableSpace (fun i ↦ f (p + i)) htail (𝓐 (j (p + n)))
      (hm.monotone (hj.monotone (Nat.le_add_right p n)) _ hsupport)
  apply nat_singletons_obstruction (d := d)
  · intro n k hnk s hs
    change MeasurableSet[𝓐 (j (p + n))] (blockUnion (fun i ↦ f (p + i)) s) at hs
    change MeasurableSet[𝓐 (j (p + k))] (blockUnion (fun i ↦ f (p + i)) s)
    exact hm.monotone (hj.monotone (Nat.add_le_add_left hnk p)) _ hs
  · intro n
    change MeasurableSet[𝓐 (j (p + (n + 1)))] (blockUnion (fun i ↦ f (p + i)) {n})
    simpa [blockUnion, Nat.add_assoc] using hfm (p + n)
  · intro n hn
    apply hfn (p + n)
    change MeasurableSet[d n] {n} at hn
    change MeasurableSet[𝓐 (j (p + n))] (blockUnion (fun i ↦ f (p + i)) {n}) at hn
    simpa [blockUnion, Nat.add_assoc] using hn
  · intro s
    have hs : MeasurableSet[𝓐'] (blockUnion (fun i ↦ f (p + i)) s) :=
      MeasurableSet.biUnion (to_countable s) fun i _ ↦ hfm' (p + i)
    obtain ⟨n, hn⟩ := (hcover _).1 hs
    refine ⟨n, ?_⟩
    change MeasurableSet[𝓐 (j (p + n))] (blockUnion (fun i ↦ f (p + i)) s)
    apply hm.monotone _ _ hn
    have := hjle (p + n)
    omega

/-- A witness formulation of the Broughton--Huff theorem: the supremum of a strictly increasing
sequence of sigma-fields contains a set that is measurable in none of the sequence terms. -/
theorem proof_exists_measurableSet_iSup_not_measurableSet_of_strictMono (hm : StrictMono 𝓐) :
    ∃ s, MeasurableSet[⨆ n, 𝓐 n] s ∧ ∀ n, ¬MeasurableSet[𝓐 n] s := by
  classical
  by_contra! h
  apply false_of_measurableSet_iff_exists_of_strictMono hm (⨆ n, 𝓐 n)
  intro s
  exact ⟨h s, fun ⟨n, hn⟩ ↦ (le_iSup 𝓐 n) _ hn⟩

/-- **Broughton--Huff theorem.** The ordinary union of a strictly increasing sequence of
sigma-fields is not the collection of measurable sets of any measurable space. -/
theorem proof_not_exists_measurableSpace_iUnion_of_strictMono (hm : StrictMono 𝓐) :
    ¬ ∃ 𝓐' : MeasurableSpace α,
      ∀ s, MeasurableSet[𝓐'] s ↔ ∃ n, MeasurableSet[𝓐 n] s := by
  rintro ⟨𝓐', hcover⟩
  exact false_of_measurableSet_iff_exists_of_strictMono hm 𝓐' hcover

end BroughtonHuff
