/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Group.Indicator
import Mathlib.Data.Int.Cast.Pi
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# Measurable spaces and measurable functions

This file provides properties of measurable spaces and the functions and isomorphisms between them.
The definition of a measurable space is in `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`.

A measurable space is a set equipped with a σ-algebra, a collection of subsets closed under
complementation and countable union. A function between measurable spaces is measurable if
the preimage of each measurable subset is measurable.

σ-algebras on a fixed set `α` form a complete lattice. Here we order σ-algebras by writing `m₁ ≤ m₂`
if every set which is `m₁`-measurable is also `m₂`-measurable (that is, `m₁` is a subset of `m₂`).
In particular, any collection of subsets of `α` generates a smallest σ-algebra which contains
all of them. A function `f : α → β` induces a Galois connection between the lattices of σ-algebras
on `α` and `β`.

## Implementation notes

Measurability of a function `f : α → β` between measurable spaces is defined in terms of the
Galois connection induced by `f`.

## References

* <https://en.wikipedia.org/wiki/Measurable_space>
* <https://en.wikipedia.org/wiki/Sigma-algebra>
* <https://en.wikipedia.org/wiki/Dynkin_system>

## Tags

measurable space, σ-algebra, measurable function, dynkin system, π-λ theorem, π-system
-/

open Set MeasureTheory

universe uι

variable {α β γ : Type*} {ι : Sort uι} {s : Set α}

namespace MeasurableSpace

section Functors

variable {m m₁ m₂ : MeasurableSpace α} {m' : MeasurableSpace β} {f : α → β} {g : β → α}

/-- The forward image of a measurable space under a function. `map f m` contains the sets
  `s : Set β` whose preimage under `f` is measurable. -/
protected def map (f : α → β) (m : MeasurableSpace α) : MeasurableSpace β where
  MeasurableSet' s := MeasurableSet[m] <| f ⁻¹' s
  measurableSet_empty := m.measurableSet_empty
  measurableSet_compl _ hs := m.measurableSet_compl _ hs
  measurableSet_iUnion f hf := by simpa only [preimage_iUnion] using m.measurableSet_iUnion _ hf

lemma map_def {s : Set β} : MeasurableSet[m.map f] s ↔ MeasurableSet[m] (f ⁻¹' s) := Iff.rfl

@[simp]
theorem map_id : m.map id = m :=
  MeasurableSpace.ext fun _ => Iff.rfl

@[simp]
theorem map_comp {f : α → β} {g : β → γ} : (m.map f).map g = m.map (g ∘ f) :=
  MeasurableSpace.ext fun _ => Iff.rfl

/-- The reverse image of a measurable space under a function. `comap f m` contains the sets
  `s : Set α` such that `s` is the `f`-preimage of a measurable set in `β`. -/
protected def comap (f : α → β) (m : MeasurableSpace β) : MeasurableSpace α where
  MeasurableSet' s := ∃ s', MeasurableSet[m] s' ∧ f ⁻¹' s' = s
  measurableSet_empty := ⟨∅, m.measurableSet_empty, rfl⟩
  measurableSet_compl := fun _ ⟨s', h₁, h₂⟩ => ⟨s'ᶜ, m.measurableSet_compl _ h₁, h₂ ▸ rfl⟩
  measurableSet_iUnion s hs :=
    let ⟨s', hs'⟩ := Classical.axiom_of_choice hs
    ⟨⋃ i, s' i, m.measurableSet_iUnion _ fun i => (hs' i).left, by simp [hs']⟩

lemma measurableSet_comap {m : MeasurableSpace β} :
    MeasurableSet[m.comap f] s ↔ ∃ s', MeasurableSet[m] s' ∧ f ⁻¹' s' = s := .rfl

theorem comap_eq_generateFrom (m : MeasurableSpace β) (f : α → β) :
    m.comap f = generateFrom { t | ∃ s, MeasurableSet s ∧ f ⁻¹' s = t } :=
  (@generateFrom_measurableSet _ (.comap f m)).symm

@[simp]
theorem comap_id : m.comap id = m :=
  MeasurableSpace.ext fun s => ⟨fun ⟨_, hs', h⟩ => h ▸ hs', fun h => ⟨s, h, rfl⟩⟩

@[simp]
theorem comap_comp {f : β → α} {g : γ → β} : (m.comap f).comap g = m.comap (f ∘ g) :=
  MeasurableSpace.ext fun _ =>
    ⟨fun ⟨_, ⟨u, h, hu⟩, ht⟩ => ⟨u, h, ht ▸ hu ▸ rfl⟩, fun ⟨t, h, ht⟩ => ⟨f ⁻¹' t, ⟨_, h, rfl⟩, ht⟩⟩

theorem comap_le_iff_le_map {f : α → β} : m'.comap f ≤ m ↔ m' ≤ m.map f :=
  ⟨fun h _s hs => h _ ⟨_, hs, rfl⟩, fun h _s ⟨_t, ht, heq⟩ => heq ▸ h _ ht⟩

theorem gc_comap_map (f : α → β) :
    GaloisConnection (MeasurableSpace.comap f) (MeasurableSpace.map f) := fun _ _ =>
  comap_le_iff_le_map

theorem map_mono (h : m₁ ≤ m₂) : m₁.map f ≤ m₂.map f :=
  (gc_comap_map f).monotone_u h

theorem monotone_map : Monotone (MeasurableSpace.map f) := fun _ _ => map_mono

theorem comap_mono (h : m₁ ≤ m₂) : m₁.comap g ≤ m₂.comap g :=
  (gc_comap_map g).monotone_l h

theorem monotone_comap : Monotone (MeasurableSpace.comap g) := fun _ _ h => comap_mono h

@[simp]
theorem comap_bot : (⊥ : MeasurableSpace α).comap g = ⊥ :=
  (gc_comap_map g).l_bot

@[simp]
theorem comap_sup : (m₁ ⊔ m₂).comap g = m₁.comap g ⊔ m₂.comap g :=
  (gc_comap_map g).l_sup

@[simp]
theorem comap_iSup {m : ι → MeasurableSpace α} : (⨆ i, m i).comap g = ⨆ i, (m i).comap g :=
  (gc_comap_map g).l_iSup

@[simp]
theorem map_top : (⊤ : MeasurableSpace α).map f = ⊤ :=
  (gc_comap_map f).u_top

@[simp]
theorem map_inf : (m₁ ⊓ m₂).map f = m₁.map f ⊓ m₂.map f :=
  (gc_comap_map f).u_inf

@[simp]
theorem map_iInf {m : ι → MeasurableSpace α} : (⨅ i, m i).map f = ⨅ i, (m i).map f :=
  (gc_comap_map f).u_iInf

theorem comap_map_le : (m.map f).comap f ≤ m :=
  (gc_comap_map f).l_u_le _

theorem le_map_comap : m ≤ (m.comap g).map g :=
  (gc_comap_map g).le_u_l _

end Functors

@[simp] theorem map_const {m} (b : β) : MeasurableSpace.map (fun _a : α ↦ b) m = ⊤ :=
  eq_top_iff.2 <| fun s _ ↦ by rw [map_def]; by_cases h : b ∈ s <;> simp [h]

@[simp] theorem comap_const {m} (b : β) : MeasurableSpace.comap (fun _a : α => b) m = ⊥ :=
  eq_bot_iff.2 <| by rintro _ ⟨s, -, rfl⟩; by_cases b ∈ s <;> simp [*]

theorem comap_generateFrom {f : α → β} {s : Set (Set β)} :
    (generateFrom s).comap f = generateFrom (preimage f '' s) :=
  le_antisymm
    (comap_le_iff_le_map.2 <|
      generateFrom_le fun _t hts => GenerateMeasurable.basic _ <| mem_image_of_mem _ <| hts)
    (generateFrom_le fun _t ⟨u, hu, Eq⟩ => Eq ▸ ⟨u, GenerateMeasurable.basic _ hu, rfl⟩)

/--
If `F : δ → Set α` is pairwise-disjoint and covers the whole space,
then every set in the σ-algebra generated by the blocks is a disjoint union
of some of those blocks.
-/
lemma measurable_eq_iUnion_of_blocks'
    {α δ : Type*}{F : δ → Set α}
    (h_disj  : Pairwise (fun i j ↦ Disjoint (F i) (F j)))
    (h_cover : (⋃ i, F i) = (Set.univ : Set α)) :
  ∀ {S : Set α},
    MeasurableSet[MeasurableSpace.generateFrom {F i | i : δ}] S →
    ∃ γ : Set δ, S = ⋃ i ∈ γ, F i :=
by
  let P : Set α → Prop := fun S ↦ ∃ γ : Set δ, S = ⋃ i ∈ γ, F i
  have h_empty : P ∅ := by
    exact ⟨∅, by simp⟩
  have h_basic : ∀ i : δ, P (F i) := by
    intro i; exact ⟨{i}, by simp⟩
  have h_compl : ∀ {S}, P S → P Sᶜ := by
    rintro S ⟨γ, rfl⟩
    refine ⟨{i | i ∉ γ}, ?_⟩
    ext x
    constructor
    · intro hx
      have : x ∈ (⋃ i, F i) := by
        have : x ∈ (Set.univ : Set α) := trivial
        simp [h_cover]
      rcases mem_iUnion.1 this with ⟨i, hi⟩
      have hiγ : i ∈ γ → False := by
        intro h
        have : x ∈ ⋃ j ∈ γ, F j := mem_iUnion₂.2 ⟨i, h, hi⟩
        exact hx this
      have : i ∉ γ := by
        by_cases h' : i ∈ γ <;> simp [h', hiγ] at *
      exact mem_iUnion₂.2 ⟨i, by simpa using this, hi⟩
    · intro hx
      rcases mem_iUnion₂.1 hx with ⟨i, hiNot, hi⟩
      intro hIn
      have hFalse : False := by
        rcases mem_iUnion₂.1 hIn with ⟨j, hjγ, hxj⟩
        by_cases hji : j = i
        · have : i ∈ γ := by simpa [hji] using hjγ
          exact hiNot this
        · have hdis : Disjoint (F i) (F j) := (h_disj hji).symm
          have hFalse : False :=
            -- `Set.disjoint_left` gives `x ∉ F j` from `x ∈ F i`
            (Set.disjoint_left.1 hdis hi) hxj
          exact hFalse.elim
      exact hFalse.elim
  have h_iUnion : ∀ f : ℕ → Set α, (∀ n, P (f n)) → P (⋃ n, f n) := by
    intro f hf
    choose γ hγ using hf
    refine ⟨⋃ n, γ n, ?_⟩
    ext x
    constructor
    · intro hx
      rcases mem_iUnion.1 hx with ⟨n, hn⟩
      have : x ∈ ⋃ i ∈ γ n, F i := by
        simpa [hγ n] using hn
      rcases mem_iUnion₂.1 this with ⟨i, hiγn, hi⟩
      exact mem_iUnion₂.2 ⟨i, mem_iUnion.2 ⟨n, hiγn⟩, hi⟩
    · intro hx
      rcases mem_iUnion₂.1 hx with ⟨i, hgi, hiF⟩
      rcases mem_iUnion.1 hgi with ⟨n, hiγn⟩
      have : x ∈ ⋃ j ∈ γ n, F j := mem_iUnion₂.2 ⟨i, hiγn, hiF⟩
      have : x ∈ f n := by
        simpa [hγ n] using this
      exact mem_iUnion.2 ⟨n, this⟩
  let blocksSpace : MeasurableSpace α :=
    { MeasurableSet'      := P,
      measurableSet_empty := h_empty,
      measurableSet_compl := by
        intro S hS; exact h_compl hS,
      measurableSet_iUnion := h_iUnion }
  have h_le : MeasurableSpace.generateFrom {F i | i : δ} ≤ blocksSpace := by
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨i, rfl⟩
    simpa using h_basic i
  intro S hS
  have : P S := (h_le _ hS)
  exact this

/-- If `m` is a strictly monotone sequence of σ-algebras, then there exists a sequence of disjoint
sets `F n` such that `F n` is `m (n + 1)`-measurable but not `m n`-measurable. -/
lemma exists_disjoint_measurable_set_of_strict_mono {m : ℕ → MeasurableSpace α}
    (h_mono : StrictMono m) :
    ∃ F : ℕ → Set α,
      (∀ n, MeasurableSet[m (n + 1)] (F n)) ∧
      (∀ n, ¬ MeasurableSet[m n] (F n)) ∧
      Pairwise (fun i j => Disjoint (F i) (F j)) := by
  sorry

/-- A theorem by Broughton and Huff: the union of a strictly increasing sequence of σ-algebras is
not a σ-algebra. -/
theorem iUnion_of_strict_mono_measurable_space_is_not_a_measurable_space
  {m : ℕ → MeasurableSpace α} (h_mono : StrictMono m) :
  ¬∃ m' : MeasurableSpace α, {s | MeasurableSet[m'] s} = ⋃ n, { s | MeasurableSet[m n] s } := by
  intro h_exists
  rcases h_exists with ⟨m', h_eq⟩
  rcases exists_disjoint_measurable_set_of_strict_mono h_mono with
    ⟨C, hC_succ_measurable, hC_not_measurable, hC_disjoint⟩
  have hC_measurable_in_m' : ∀ n, MeasurableSet[m'] (C n) := by
    intro n
    have : (C n) ∈ {s | MeasurableSet[m (n + 1)] s} := by
      simpa using hC_succ_measurable n
    have : (C n) ∈ ⋃ k, {s | MeasurableSet[m k] s} :=
      mem_iUnion.mpr ⟨n + 1, this⟩
    simpa [← h_eq] using this
  let F : Set α := ⋃ n : ℕ, C n
  have h_unionC_measurable_in_m' : MeasurableSet[m'] F := by
    have : ∀ n, MeasurableSet[m'] (C n) := hC_measurable_in_m'
    exact MeasurableSet.iUnion this
  have h_unionC_in_chain :
      F ∈ ⋃ k, {s | MeasurableSet[m k] s} := by
    simpa [← h_eq] using h_unionC_measurable_in_m'
  rcases mem_iUnion.mp h_unionC_in_chain with ⟨k, hk⟩
  let Fσ₀ : MeasurableSpace α := generateFrom { C n | n : ℕ }
  let B := fun n ↦
      sInf {A : Set α | C n ⊆ A ∧ MeasurableSet[m n] A ∧ MeasurableSet[Fσ₀] A}
  have hB_adm :
      ∀ n : ℕ,
        B n ∈ {A : Set α |
                C n ⊆ A ∧
                MeasurableSet[m n] A ∧
                MeasurableSet[Fσ₀] A} := by
    sorry
  have h_Ci_not_subset_Bj :
    ∀ {i j : ℕ}, i < j → ¬ (C i ⊆ B j) := by
    intro i j hij hsub
    -- Work with `A := B j \ C i`
    let A : Set α := B j \ C i

    -- Basic data for `B j` obtained in one shot from `hB_adm`
    have hB_adm_j := hB_adm j
    have hCj_sub_Bj : C j ⊆ B j           := hB_adm_j.1
    have hBj_meas_mj : MeasurableSet[m j] (B j) := hB_adm_j.2.1
    have hBj_meas_F  : MeasurableSet[Fσ₀] (B j) := hB_adm_j.2.2

    -- 1.  `C j ⊆ A`
    have h₁ : C j ⊆ A := by
      intro x hxCj
      have hx_Bj : x ∈ B j := hCj_sub_Bj hxCj
      have hdisj : Disjoint (C i) (C j) := hC_disjoint hij.ne
      have hx_not_Ci : x ∉ C i := by
        have hdl := disjoint_left.1 hdisj; intro hxCi; exact hdl hxCi hxCj
      exact ⟨hx_Bj, hx_not_Ci⟩

    -- 2.  measurability of `A` in `m j`
    have hCi_meas_mj : MeasurableSet[m j] (C i) := by
      have hCi_meas_mip1 := hC_succ_measurable i
      have hle : m (i + 1) ≤ m j := h_mono.monotone (Nat.succ_le_of_lt hij)
      exact hle _ hCi_meas_mip1
    have h₂ : MeasurableSet[m j] A := by
      have : A = B j ∩ (C i)ᶜ := by
        ext x; simp [A, Set.mem_diff]
      simpa [this] using hBj_meas_mj.inter (hCi_meas_mj.compl)

    -- 3.  measurability of `A` in `Fσ₀`
    have hCi_meas_F : MeasurableSet[Fσ₀] (C i) := by
      have hmem : (C i) ∈ ({C k | k : ℕ} : Set (Set α)) := by simp
      have : MeasurableSet[MeasurableSpace.generateFrom {C k | k : ℕ}] (C i) :=
        MeasurableSpace.measurableSet_generateFrom hmem
      simpa [Fσ₀] using this
    have h₃ : MeasurableSet[Fσ₀] A := by
      have : A = B j ∩ (C i)ᶜ := by
        ext x; simp [A, Set.mem_diff]
      simpa [this] using hBj_meas_F.inter (hCi_meas_F.compl)

    -- 4.  `A` is admissible ⇒ minimality of `B j` ⇒ contradiction
    have hA_adm :
        A ∈ {S : Set α |
              C j ⊆ S ∧ MeasurableSet[m j] S ∧ MeasurableSet[Fσ₀] S} :=
      ⟨h₁, h₂, h₃⟩
    have hBj_sub_A : B j ⊆ A := by
      have : sInf {S : Set α |
                      C j ⊆ S ∧
                      MeasurableSet[m j] S ∧
                      MeasurableSet[Fσ₀] S} ⊆ A :=
        sInf_le hA_adm
      simpa [B] using this

    -- 5.  pick `x ∈ C i`, derive contradiction
    have hCi_nonempty : (C i).Nonempty := by
      by_contra h
      have hCi_meas : MeasurableSet[m i] (C i) := by
        simp [Set.not_nonempty_iff_eq_empty.mp h]
      exact (hC_not_measurable i) hCi_meas
    rcases hCi_nonempty with ⟨x, hxCi⟩
    have hxBj : x ∈ B j := hsub hxCi
    have hx_not_A : x ∉ A := by simp [A, hxCi]
    exact hx_not_A (hBj_sub_A hxBj)

  have h_exists_later_subset :
    ∀ n : ℕ, ∃ j : ℕ, n < j ∧ C j ⊆ B n := by
    intro n
    have hBn_ne_Cn : (B n) ≠ C n := by
      intro h_eq
      have : MeasurableSet[m n] (C n) := by
        simpa [h_eq] using (hB_adm n).2.1
      exact (hC_not_measurable n) this
    have hdiff : (B n \ C n).Nonempty := by
      have : (B n \ C n) ≠ ∅ := by
        intro h_eq
        have : B n ⊆ C n := by
          intro x hxBn
          by_cases hxCn : x ∈ C n
          · exact hxCn
          · have : x ∈ (B n \ C n) := ⟨hxBn, hxCn⟩
            simp [h_eq] at this
        have : B n = C n := Set.Subset.antisymm this ((hB_adm n).1)
        exact hBn_ne_Cn this
      exact Set.nonempty_iff_ne_empty.mpr this

    rcases hdiff with ⟨x, hxBn, hx_not_Cn⟩
    -- locate the unique generator that contains x
    rcases mem_iUnion.mp (by
        have : x ∈ F := by
          dsimp [F]; exact mem_iUnion.mpr ⟨n, hxBn⟩
        simpa [F] using this)
      with ⟨j, hxCj⟩
    have hj_ne : j ≠ n := by
      intro h_eq; exact hx_not_Cn (by simpa [h_eq] using hxCj)

    ------------------------------------------------------------
    -- Step 2 : prove C j ⊆ B n  (*** fill this in ***)
    ------------------------------------------------------------
    have hCj_subset_Bn : C j ⊆ B n := by
      sorry

    ------------------------------------------------------------
    -- Step 3 : j must be strictly larger than n
    ------------------------------------------------------------
    have h_lt : n < j := by
      have h_le : j ≤ n ∨ n < j := le_or_lt j n
      cases h_le with
      | inl hle =>
          have hlt_or_eq := lt_or_eq_of_le hle
          cases hlt_or_eq with
          | inl hlt =>
              -- would violate `h_Ci_not_subset_Bj`
              exact (h_Ci_not_subset_Bj hlt hCj_subset_Bn).elim
          | inr h_eq =>
              exact (hj_ne h_eq).elim
      | inr hlt => exact hlt

    exact ⟨j, h_lt, hCj_subset_Bn⟩
  sorry

end MeasurableSpace

section MeasurableFunctions

open MeasurableSpace

theorem measurable_iff_le_map {m₁ : MeasurableSpace α} {m₂ : MeasurableSpace β} {f : α → β} :
    Measurable f ↔ m₂ ≤ m₁.map f :=
  Iff.rfl

alias ⟨Measurable.le_map, Measurable.of_le_map⟩ := measurable_iff_le_map

theorem measurable_iff_comap_le {m₁ : MeasurableSpace α} {m₂ : MeasurableSpace β} {f : α → β} :
    Measurable f ↔ m₂.comap f ≤ m₁ :=
  comap_le_iff_le_map.symm

alias ⟨Measurable.comap_le, Measurable.of_comap_le⟩ := measurable_iff_comap_le

theorem comap_measurable {m : MeasurableSpace β} (f : α → β) : Measurable[m.comap f] f :=
  fun s hs => ⟨s, hs, rfl⟩

theorem Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : MeasurableSpace β} {f : α → β}
    (hf : @Measurable α β ma mb f) (ha : ma ≤ ma') (hb : mb' ≤ mb) : @Measurable α β ma' mb' f :=
  fun _t ht => ha _ <| hf <| hb _ ht

lemma Measurable.iSup' {mα : ι → MeasurableSpace α} {_ : MeasurableSpace β} {f : α → β} (i₀ : ι)
    (h : Measurable[mα i₀] f) :
    Measurable[⨆ i, mα i] f :=
  h.mono (le_iSup mα i₀) le_rfl

lemma Measurable.sup_of_left {mα mα' : MeasurableSpace α} {_ : MeasurableSpace β} {f : α → β}
    (h : Measurable[mα] f) :
    Measurable[mα ⊔ mα'] f :=
  h.mono le_sup_left le_rfl

lemma Measurable.sup_of_right {mα mα' : MeasurableSpace α} {_ : MeasurableSpace β} {f : α → β}
    (h : Measurable[mα'] f) :
    Measurable[mα ⊔ mα'] f :=
  h.mono le_sup_right le_rfl

theorem measurable_id'' {m mα : MeasurableSpace α} (hm : m ≤ mα) : @Measurable α α mα m id :=
  measurable_id.mono le_rfl hm

@[measurability]
theorem measurable_from_top [MeasurableSpace β] {f : α → β} : Measurable[⊤] f := fun _ _ => trivial

theorem measurable_generateFrom [MeasurableSpace α] {s : Set (Set β)} {f : α → β}
    (h : ∀ t ∈ s, MeasurableSet (f ⁻¹' t)) : @Measurable _ _ _ (generateFrom s) f :=
  Measurable.of_le_map <| generateFrom_le h

variable {f g : α → β}

section TypeclassMeasurableSpace

variable [MeasurableSpace α] [MeasurableSpace β]

@[nontriviality, measurability]
theorem Subsingleton.measurable [Subsingleton α] : Measurable f := fun _ _ =>
  @Subsingleton.measurableSet α _ _ _

@[nontriviality, measurability]
theorem measurable_of_subsingleton_codomain [Subsingleton β] (f : α → β) : Measurable f :=
  fun s _ => Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s

@[to_additive (attr := measurability, fun_prop)]
theorem measurable_one [One α] : Measurable (1 : β → α) :=
  @measurable_const _ _ _ _ 1

theorem measurable_of_empty [IsEmpty α] (f : α → β) : Measurable f :=
  Subsingleton.measurable

theorem measurable_of_empty_codomain [IsEmpty β] (f : α → β) : Measurable f :=
  measurable_of_subsingleton_codomain f

/-- A version of `measurable_const` that assumes `f x = f y` for all `x, y`. This version works
for functions between empty types. -/
theorem measurable_const' {f : β → α} (hf : ∀ x y, f x = f y) : Measurable f := by
  nontriviality β
  inhabit β
  convert @measurable_const α β _ _ (f default) using 2
  apply hf

@[measurability]
theorem measurable_natCast [NatCast α] (n : ℕ) : Measurable (n : β → α) :=
  @measurable_const α _ _ _ n

@[measurability]
theorem measurable_intCast [IntCast α] (n : ℤ) : Measurable (n : β → α) :=
  @measurable_const α _ _ _ n

theorem measurable_of_countable [Countable α] [MeasurableSingletonClass α] (f : α → β) :
    Measurable f := fun s _ =>
  (f ⁻¹' s).to_countable.measurableSet

theorem measurable_of_finite [Finite α] [MeasurableSingletonClass α] (f : α → β) : Measurable f :=
  measurable_of_countable f

end TypeclassMeasurableSpace

variable {m : MeasurableSpace α}

@[measurability]
theorem Measurable.iterate {f : α → α} (hf : Measurable f) : ∀ n, Measurable f^[n]
  | 0 => measurable_id
  | n + 1 => (Measurable.iterate hf n).comp hf

variable {mβ : MeasurableSpace β}

@[measurability]
theorem measurableSet_preimage {t : Set β} (hf : Measurable f) (ht : MeasurableSet t) :
    MeasurableSet (f ⁻¹' t) :=
  hf ht

protected theorem MeasurableSet.preimage {t : Set β} (ht : MeasurableSet t) (hf : Measurable f) :
    MeasurableSet (f ⁻¹' t) :=
  hf ht

@[measurability, fun_prop]
protected theorem Measurable.piecewise {_ : DecidablePred (· ∈ s)} (hs : MeasurableSet s)
    (hf : Measurable f) (hg : Measurable g) : Measurable (piecewise s f g) := by
  intro t ht
  rw [piecewise_preimage]
  exact hs.ite (hf ht) (hg ht)

/-- This is slightly different from `Measurable.piecewise`. It can be used to show
`Measurable (ite (x=0) 0 1)` by
`exact Measurable.ite (measurableSet_singleton 0) measurable_const measurable_const`,
but replacing `Measurable.ite` by `Measurable.piecewise` in that example proof does not work. -/
theorem Measurable.ite {p : α → Prop} {_ : DecidablePred p} (hp : MeasurableSet { a : α | p a })
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => ite (p x) (f x) (g x) :=
  Measurable.piecewise hp hf hg

@[measurability, fun_prop]
theorem Measurable.indicator [Zero β] (hf : Measurable f) (hs : MeasurableSet s) :
    Measurable (s.indicator f) :=
  hf.piecewise hs measurable_const

/-- The measurability of a set `A` is equivalent to the measurability of the indicator function
which takes a constant value `b ≠ 0` on a set `A` and `0` elsewhere. -/
lemma measurable_indicator_const_iff [Zero β] [MeasurableSingletonClass β] (b : β) [NeZero b] :
    Measurable (s.indicator (fun (_ : α) ↦ b)) ↔ MeasurableSet s := by
  constructor <;> intro h
  · convert h (MeasurableSet.singleton (0 : β)).compl
    ext a
    simp [NeZero.ne b]
  · exact measurable_const.indicator h

@[to_additive (attr := measurability)]
theorem measurableSet_mulSupport [One β] [MeasurableSingletonClass β] (hf : Measurable f) :
    MeasurableSet (Function.mulSupport f) :=
  hf (measurableSet_singleton 1).compl

/-- If a function coincides with a measurable function outside of a countable set, it is
measurable. -/
theorem Measurable.measurable_of_countable_ne [MeasurableSingletonClass α] (hf : Measurable f)
    (h : Set.Countable { x | f x ≠ g x }) : Measurable g := by
  intro t ht
  have : g ⁻¹' t = g ⁻¹' t ∩ { x | f x = g x }ᶜ ∪ g ⁻¹' t ∩ { x | f x = g x } := by
    simp [← inter_union_distrib_left]
  rw [this]
  refine (h.mono inter_subset_right).measurableSet.union ?_
  have : g ⁻¹' t ∩ { x : α | f x = g x } = f ⁻¹' t ∩ { x : α | f x = g x } := by
    ext x
    simp +contextual
  rw [this]
  exact (hf ht).inter h.measurableSet.of_compl

end MeasurableFunctions

/-- We say that a collection of sets is countably spanning if a countable subset spans the
whole type. This is a useful condition in various parts of measure theory. For example, it is
a needed condition to show that the product of two collections generate the product sigma algebra,
see `generateFrom_prod_eq`. -/
def IsCountablySpanning (C : Set (Set α)) : Prop :=
  ∃ s : ℕ → Set α, (∀ n, s n ∈ C) ∧ ⋃ n, s n = univ

theorem isCountablySpanning_measurableSet [MeasurableSpace α] :
    IsCountablySpanning { s : Set α | MeasurableSet s } :=
  ⟨fun _ => univ, fun _ => MeasurableSet.univ, iUnion_const _⟩

/-- Rectangles of countably spanning sets are countably spanning. -/
lemma IsCountablySpanning.prod {C : Set (Set α)} {D : Set (Set β)} (hC : IsCountablySpanning C)
    (hD : IsCountablySpanning D) : IsCountablySpanning (image2 (· ×ˢ ·) C D) := by
  rcases hC, hD with ⟨⟨s, h1s, h2s⟩, t, h1t, h2t⟩
  refine ⟨fun n => s n.unpair.1 ×ˢ t n.unpair.2, fun n => mem_image2_of_mem (h1s _) (h1t _), ?_⟩
  rw [iUnion_unpair_prod, h2s, h2t, univ_prod_univ]
