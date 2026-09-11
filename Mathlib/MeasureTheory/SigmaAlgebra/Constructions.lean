/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Update
public import Mathlib.Data.Prod.TProd
public import Mathlib.Data.Set.UnionLift
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.MeasureTheory.SigmaAlgebra.Basic
public import Mathlib.MeasureTheory.SigmaAlgebra.Instances
public import Mathlib.Order.Disjointed

/-!
# Constructions for measurable spaces and functions

This file provides several ways to construct new measurable spaces and functions from old ones:
`Quotient`, `Subtype`, `Prod`, `Pi`, etc.
-/

@[expose] public section

assert_not_exists Filter

open Set Function

universe uι

variable {α β γ δ δ' : Type*} {ι : Sort uι} {s : Set α}

theorem measurable_to_countable [SigmaAlgebra α] [Countable α] [SigmaAlgebra β] {f : β → α}
    (h : ∀ y, MeasurableSet (f ⁻¹' {f y})) : Measurable f := fun s _ => by
  rw [← biUnion_preimage_singleton]
  refine MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun hy => ?_
  by_cases hyf : y ∈ range f
  · rcases hyf with ⟨y, rfl⟩
    apply h
  · simp only [preimage_singleton_eq_empty.2 hyf, MeasurableSet.empty]

theorem measurable_to_countable' [SigmaAlgebra α] [Countable α] [SigmaAlgebra β] {f : β → α}
    (h : ∀ x, MeasurableSet (f ⁻¹' {x})) : Measurable f :=
  measurable_to_countable fun y => h (f y)

set_option backward.isDefEq.respectTransparency false in
theorem ENat.measurable_iff {α : Type*} [SigmaAlgebra α] {f : α → ℕ∞} :
    Measurable f ↔ ∀ n : ℕ, MeasurableSet (f ⁻¹' {↑n}) := by
  refine ⟨fun hf n ↦ hf <| measurableSet_singleton _, fun h ↦ measurable_to_countable' fun n ↦ ?_⟩
  cases n with
  | top =>
    rw [← WithTop.none_eq_top, ← compl_range_some, preimage_compl, ← iUnion_singleton_eq_range,
      preimage_iUnion]
    exact .compl <| .iUnion h
  | coe n => exact h n

theorem measurable_unit [SigmaAlgebra α] (f : Unit → α) : Measurable f :=
  measurable_from_top

section ULift
variable [SigmaAlgebra α]

instance _root_.ULift.instSigmaAlgebra : SigmaAlgebra (ULift α) :=
  ‹SigmaAlgebra α›.map ULift.up

lemma measurable_down : Measurable (ULift.down : ULift α → α) := fun _ ↦ id
lemma measurable_up : Measurable (ULift.up : α → ULift α) := fun _ ↦ id

@[simp] lemma measurableSet_preimage_down {s : Set α} :
    MeasurableSet (ULift.down ⁻¹' s) ↔ MeasurableSet s := Iff.rfl
@[simp] lemma measurableSet_preimage_up {s : Set (ULift α)} :
    MeasurableSet (ULift.up ⁻¹' s) ↔ MeasurableSet s := Iff.rfl

end ULift

section Nat

variable {mα : SigmaAlgebra α}

theorem measurable_from_nat {f : ℕ → α} : Measurable f :=
  measurable_from_top

theorem measurable_to_nat {f : α → ℕ} : (∀ y, MeasurableSet (f ⁻¹' {f y})) → Measurable f :=
  measurable_to_countable

theorem measurable_to_bool {f : α → Bool} (h : MeasurableSet (f ⁻¹' {true})) : Measurable f := by
  apply measurable_to_countable'
  rintro (- | -)
  · convert! h.compl
    rw [← preimage_compl, Bool.compl_singleton, Bool.not_true]
  exact h

theorem measurable_to_prop {f : α → Prop} (h : MeasurableSet (f ⁻¹' {True})) : Measurable f := by
  refine measurable_to_countable' fun x => ?_
  by_cases hx : x
  · simpa [hx] using h
  · simpa only [hx, ← preimage_compl, Prop.compl_singleton, not_true, preimage_singleton_false]
      using h.compl

theorem measurable_findGreatest' {p : α → ℕ → Prop} [∀ x, DecidablePred (p x)] {N : ℕ}
    (hN : ∀ k ≤ N, MeasurableSet { x | Nat.findGreatest (p x) N = k }) :
    Measurable fun x => Nat.findGreatest (p x) N :=
  measurable_to_nat fun _ => hN _ N.findGreatest_le

theorem measurable_findGreatest {p : α → ℕ → Prop} [∀ x, DecidablePred (p x)] {N}
    (hN : ∀ k ≤ N, MeasurableSet { x | p x k }) : Measurable fun x => Nat.findGreatest (p x) N := by
  refine measurable_findGreatest' fun k hk => ?_
  simp only [Nat.findGreatest_eq_iff, ofPred_and, ofPred_forall, ← compl_ofPred]
  repeat' apply_rules [MeasurableSet.inter, MeasurableSet.const, MeasurableSet.iInter,
    MeasurableSet.compl, hN] <;> try intros

@[simp, measurability]
protected theorem MeasurableSet.disjointed {f : ℕ → Set α} (h : ∀ i, MeasurableSet (f i)) (n) :
    MeasurableSet (disjointed f n) :=
  disjointedRec (fun _ _ ht => MeasurableSet.diff ht <| h _) (h n)

theorem measurable_find {p : α → ℕ → Prop} [∀ x, DecidablePred (p x)] (hp : ∀ x, ∃ N, p x N)
    (hm : ∀ k, MeasurableSet { x | p x k }) : Measurable fun x => Nat.find (hp x) := by
  refine measurable_to_nat fun x => ?_
  rw [preimage_find_eq_disjointed (fun k => {x | p x k})]
  exact MeasurableSet.disjointed hm _

end Nat

section Quotient

variable [SigmaAlgebra α] [SigmaAlgebra β]

instance Quot.instSigmaAlgebra {α} {r : α → α → Prop} [m : SigmaAlgebra α] :
    SigmaAlgebra (Quot r) :=
  m.map (Quot.mk r)

instance Quotient.instSigmaAlgebra {α} {s : Setoid α} [m : SigmaAlgebra α] :
    SigmaAlgebra (Quotient s) :=
  m.map Quotient.mk''

@[to_additive]
instance QuotientGroup.sigmaAlgebra {G} [Group G] [SigmaAlgebra G] (S : Subgroup G) :
    SigmaAlgebra (G ⧸ S) :=
  Quotient.instSigmaAlgebra

theorem measurableSet_quotient {s : Setoid α} {t : Set (Quotient s)} :
    MeasurableSet t ↔ MeasurableSet (Quotient.mk'' ⁻¹' t) :=
  Iff.rfl

theorem measurable_from_quotient {s : Setoid α} {f : Quotient s → β} :
    Measurable f ↔ Measurable (f ∘ Quotient.mk'') :=
  Iff.rfl

@[fun_prop]
theorem measurable_quotient_mk' [s : Setoid α] : Measurable (Quotient.mk' : α → Quotient s) :=
  fun _ => id

@[fun_prop]
theorem measurable_quotient_mk'' {s : Setoid α} : Measurable (Quotient.mk'' : α → Quotient s) :=
  fun _ => id

@[fun_prop]
theorem measurable_quot_mk {r : α → α → Prop} : Measurable (Quot.mk r) := fun _ => id

@[to_additive (attr := fun_prop)]
theorem QuotientGroup.measurable_coe {G} [Group G] [SigmaAlgebra G] {S : Subgroup G} :
    Measurable ((↑) : G → G ⧸ S) :=
  measurable_quotient_mk''

@[to_additive]
nonrec theorem QuotientGroup.measurable_from_quotient {G} [Group G] [SigmaAlgebra G]
    {S : Subgroup G} {f : G ⧸ S → α} : Measurable f ↔ Measurable (f ∘ ((↑) : G → G ⧸ S)) :=
  measurable_from_quotient

instance Quotient.instDiscreteSigmaAlgebra {α} {s : Setoid α} [SigmaAlgebra α]
    [DiscreteSigmaAlgebra α] : DiscreteSigmaAlgebra (Quotient s) where
  forall_measurableSet _ := measurableSet_quotient.2 .of_discrete

@[to_additive]
instance QuotientGroup.instDiscreteSigmaAlgebra {G} [Group G] [SigmaAlgebra G]
    [DiscreteSigmaAlgebra G] (S : Subgroup G) : DiscreteSigmaAlgebra (G ⧸ S) :=
  Quotient.instDiscreteSigmaAlgebra

end Quotient

section Subtype

instance Subtype.instSigmaAlgebra {α} {p : α → Prop} [m : SigmaAlgebra α] :
    SigmaAlgebra (Subtype p) :=
  m.comap ((↑) : _ → α)

section

variable [SigmaAlgebra α]

theorem measurable_subtype_coe {p : α → Prop} : Measurable ((↑) : Subtype p → α) :=
  SigmaAlgebra.le_map_comap

instance Subtype.instMeasurableSingletonClass {p : α → Prop} [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Subtype p) where
  measurableSet_singleton x :=
    ⟨{(x : α)}, measurableSet_singleton (x : α), by
      rw [← image_singleton, preimage_image_eq _ Subtype.val_injective]⟩

end

variable {m : SigmaAlgebra α} {mβ : SigmaAlgebra β}

theorem MeasurableSet.of_subtype_image {s : Set α} {t : Set s}
    (h : MeasurableSet (Subtype.val '' t)) : MeasurableSet t :=
  ⟨_, h, preimage_image_eq _ Subtype.val_injective⟩

theorem MeasurableSet.subtype_image {s : Set α} {t : Set s} (hs : MeasurableSet s) :
    MeasurableSet t → MeasurableSet (((↑) : s → α) '' t) := by
  rintro ⟨u, hu, rfl⟩
  rw [Subtype.image_preimage_coe]
  exact hs.inter hu

@[fun_prop]
theorem Measurable.subtype_coe {p : β → Prop} {f : α → Subtype p} (hf : Measurable f) :
    Measurable fun a : α => (f a : β) :=
  measurable_subtype_coe.comp hf

alias Measurable.subtype_val := Measurable.subtype_coe

@[fun_prop]
theorem Measurable.subtype_mk {p : β → Prop} {f : α → β} (hf : Measurable f) {h : ∀ x, p (f x)} :
    Measurable fun x => (⟨f x, h x⟩ : Subtype p) := fun t ⟨s, hs⟩ =>
  hs.2 ▸ by simp only [← preimage_comp, Function.comp_def, hf hs.1]

@[fun_prop]
theorem Measurable.codRestrict {s : Set β} {f : α → β} (hf : Measurable f)
    (h : ∀ y, f y ∈ s) : Measurable (codRestrict f s h) := hf.subtype_mk

@[fun_prop]
protected theorem Measurable.rangeFactorization {f : α → β} (hf : Measurable f) :
    Measurable (rangeFactorization f) :=
  hf.subtype_mk

theorem Measurable.subtype_map {f : α → β} {p : α → Prop} {q : β → Prop} (hf : Measurable f)
    (hpq : ∀ x, p x → q (f x)) : Measurable (Subtype.map f hpq) :=
  (hf.comp measurable_subtype_coe).subtype_mk

theorem measurable_inclusion {s t : Set α} (h : s ⊆ t) : Measurable (inclusion h) :=
  measurable_id.subtype_map h

theorem MeasurableSet.image_inclusion' {s t : Set α} (h : s ⊆ t) {u : Set s}
    (hs : MeasurableSet (Subtype.val ⁻¹' s : Set t)) (hu : MeasurableSet u) :
    MeasurableSet (inclusion h '' u) := by
  rcases hs with ⟨v, hv, hvs⟩
  rcases hu with ⟨u, hu, rfl⟩
  refine ⟨u ∩ v, m.inter_mem hu hv, ?_⟩
  ext ⟨x, hx⟩
  have hxvs : x ∈ v ↔ x ∈ s := by
    simpa using Set.ext_iff.mp hvs ⟨x, hx⟩
  simp [hxvs, and_comm]

theorem MeasurableSet.image_inclusion {s t : Set α} (h : s ⊆ t) {u : Set s}
    (hs : MeasurableSet s) (hu : MeasurableSet u) :
    MeasurableSet (inclusion h '' u) :=
  MeasurableSet.image_inclusion' h (measurable_subtype_coe hs) hu

theorem MeasurableSet.of_union_cover {s t u : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : univ ⊆ s ∪ t) (hsu : MeasurableSet (((↑) : s → α) ⁻¹' u))
    (htu : MeasurableSet (((↑) : t → α) ⁻¹' u)) : MeasurableSet u := by
  convert! (hs.subtype_image hsu).union (ht.subtype_image htu)
  simp [image_preimage_eq_inter_range, ← inter_union_distrib_left, univ_subset_iff.1 h]

theorem measurable_of_measurable_union_cover {f : α → β} (s t : Set α) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h : univ ⊆ s ∪ t) (hc : Measurable fun a : s => f a)
    (hd : Measurable fun a : t => f a) : Measurable f := fun _u hu =>
  MeasurableSet.of_union_cover hs ht h (hc hu) (hd hu)

theorem measurable_of_restrict_of_restrict_compl {f : α → β} {s : Set α} (hs : MeasurableSet s)
    (h₁ : Measurable (s.domRestrict f)) (h₂ : Measurable (sᶜ.domRestrict f)) : Measurable f :=
  measurable_of_measurable_union_cover s sᶜ hs hs.compl (union_compl_self s).ge h₁ h₂

theorem Measurable.dite [∀ x, Decidable (x ∈ s)] {f : s → β} (hf : Measurable f)
    {g : (sᶜ : Set α) → β} (hg : Measurable g) (hs : MeasurableSet s) :
    Measurable fun x => if hx : x ∈ s then f ⟨x, hx⟩ else g ⟨x, hx⟩ :=
  measurable_of_restrict_of_restrict_compl hs (by simpa) (by simpa)

theorem measurable_of_measurable_on_compl_finite [MeasurableSingletonClass α] {f : α → β}
    (s : Set α) (hs : s.Finite) (hf : Measurable (sᶜ.domRestrict f)) : Measurable f :=
  have := hs.to_subtype
  measurable_of_restrict_of_restrict_compl hs.measurableSet (measurable_of_finite _) hf

theorem measurable_of_measurable_on_compl_countable [MeasurableSingletonClass α] {f : α → β}
    (s : Set α) (hs : s.Countable) (hf : Measurable (sᶜ.domRestrict f)) : Measurable f :=
  have := hs.to_subtype
  measurable_of_restrict_of_restrict_compl hs.measurableSet (measurable_of_countable _) hf

theorem measurable_of_measurable_on_compl_singleton [MeasurableSingletonClass α] {f : α → β} (a : α)
    (hf : Measurable ({ x | x ≠ a }.domRestrict f)) : Measurable f :=
  measurable_of_measurable_on_compl_finite {a} (finite_singleton a) hf

end Subtype

section IndistinguishabilityClasses

namespace SigmaAlgebra

/-- Two points are indistinguishable by `m` if they have the same membership pattern on its
sets. -/
def Indistinguishable (m : SigmaAlgebra β) (x y : β) : Prop :=
  ∀ s ∈ m, x ∈ s ↔ y ∈ s

@[refl] lemma indistinguishable_refl (m : SigmaAlgebra β) (x : β) : m.Indistinguishable x x :=
  fun _ _ ↦ Iff.rfl

@[symm] lemma Indistinguishable.symm {m : SigmaAlgebra β} {x y : β}
    (h : m.Indistinguishable x y) : m.Indistinguishable y x :=
  fun s hs ↦ (h s hs).symm

@[trans] lemma Indistinguishable.trans {m : SigmaAlgebra β} {x y z : β}
    (hxy : m.Indistinguishable x y) (hyz : m.Indistinguishable y z) :
    m.Indistinguishable x z :=
  fun s hs ↦ (hxy s hs).trans (hyz s hs)

/-- The setoid of points indistinguishable by a sigma-algebra. -/
def indistinguishabilitySetoid (m : SigmaAlgebra β) : Setoid β where
  r := m.Indistinguishable
  iseqv := ⟨m.indistinguishable_refl, Indistinguishable.symm, Indistinguishable.trans⟩

/-- The points that no set in `m` distinguishes from `x`.

This is an equivalence class for the relation of having the same membership pattern on `m`. It
need not itself belong to `m`; see `SigmaAlgebra.IsAtom` for the distinct notion of a measurable
atom. -/
def indistinguishabilityClass (m : SigmaAlgebra β) (x : β) : Set β :=
  {y | m.Indistinguishable x y}

@[simp]
lemma mem_indistinguishabilityClass_iff {m : SigmaAlgebra β} {x y : β} :
    y ∈ m.indistinguishabilityClass x ↔ m.Indistinguishable x y :=
  Iff.rfl

theorem indistinguishable_iff_forall_mem {m : SigmaAlgebra β} {x y : β} :
    m.Indistinguishable x y ↔ ∀ s ∈ m, x ∈ s ↔ y ∈ s :=
  Iff.rfl

@[simp] lemma self_mem_indistinguishabilityClass (m : SigmaAlgebra β) (x : β) :
    x ∈ m.indistinguishabilityClass x :=
  m.indistinguishable_refl x

lemma mem_of_mem_indistinguishabilityClass {m : SigmaAlgebra β} {x y : β}
    (h : y ∈ m.indistinguishabilityClass x) {s : Set β} (hs : s ∈ m) (hxs : x ∈ s) : y ∈ s :=
  (h s hs).mp hxs

lemma indistinguishabilityClass_subset {m : SigmaAlgebra β} {s : Set β} {x : β}
    (hs : s ∈ m) (hx : x ∈ s) : m.indistinguishabilityClass x ⊆ s :=
  fun _ hy ↦ mem_of_mem_indistinguishabilityClass hy hs hx

lemma indistinguishabilityClass_eq_singleton {m : SigmaAlgebra β} {x : β} (hx : {x} ∈ m) :
    m.indistinguishabilityClass x = {x} :=
  Subset.antisymm (indistinguishabilityClass_subset hx rfl)
    (fun _ hy ↦ hy ▸ m.self_mem_indistinguishabilityClass x)

@[simp]
lemma indistinguishabilityClass_of_measurableSingletonClass {m : SigmaAlgebra β}
    [@MeasurableSingletonClass β m] (x : β) : m.indistinguishabilityClass x = {x} :=
  indistinguishabilityClass_eq_singleton (measurableSet_singleton x)

lemma indistinguishabilityClass_mem_of_countable {m : SigmaAlgebra β} [Countable β]
    (x : β) : m.indistinguishabilityClass x ∈ m := by
  classical
  have : ∀ (y : β), y ∉ m.indistinguishabilityClass x →
      ∃ s, x ∈ s ∧ s ∈ m ∧ y ∉ s :=
    fun y hy ↦ by
      simp only [mem_indistinguishabilityClass_iff, Indistinguishable, not_forall,
        exists_prop] at hy
      obtain ⟨s, hs, hxy⟩ := hy
      by_cases hxs : x ∈ s
      · have hys : y ∉ s := by simpa [hxs] using hxy
        exact ⟨s, hxs, hs, hys⟩
      · have hys : y ∈ s := by simpa [hxs] using hxy
        exact ⟨sᶜ, by simpa, m.compl_mem hs, by simpa⟩
  choose! s hs using this
  have : m.indistinguishabilityClass x =
      ⋂ (y ∈ (m.indistinguishabilityClass x)ᶜ), s y := by
    apply Subset.antisymm
    · intro z hz
      simp only [mem_iInter, mem_compl_iff]
      intro i hi
      exact mem_of_mem_indistinguishabilityClass hz (hs i hi).2.1 (hs i hi).1
    · apply compl_subset_compl.1
      intro z hz
      simp only [compl_iInter, mem_iUnion, mem_compl_iff, exists_prop]
      exact ⟨z, hz, (hs z hz).2.2⟩
  rw [this]
  exact MeasurableSet.biInter (to_countable (m.indistinguishabilityClass x)ᶜ)
    (fun i hi ↦ (hs i hi).2.1)

/-- There is in fact equality: see `indistinguishabilityClass_eq_of_mem`. -/
lemma indistinguishabilityClass_subset_of_mem {m : SigmaAlgebra β} {x y : β}
    (hx : x ∈ m.indistinguishabilityClass y) :
    m.indistinguishabilityClass x ⊆ m.indistinguishabilityClass y := by
  intro z hz s hs
  exact (hx s hs).trans (hz s hs)

lemma indistinguishabilityClass_eq_of_mem {m : SigmaAlgebra β} {x y : β}
    (hx : x ∈ m.indistinguishabilityClass y) :
    m.indistinguishabilityClass x = m.indistinguishabilityClass y := by
  refine subset_antisymm (indistinguishabilityClass_subset_of_mem hx) ?_
  apply indistinguishabilityClass_subset_of_mem
  exact fun s hs ↦ (hx s hs).symm

lemma disjoint_indistinguishabilityClass_of_notMem {m : SigmaAlgebra β} {x y : β}
    (hx : x ∉ m.indistinguishabilityClass y) :
    Disjoint (m.indistinguishabilityClass x) (m.indistinguishabilityClass y) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext z
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro hzx hzy
  have h1 := indistinguishabilityClass_eq_of_mem hzx
  have h2 := indistinguishabilityClass_eq_of_mem hzy
  rw [← h2, h1] at hx
  exact hx (self_mem_indistinguishabilityClass m x)

end SigmaAlgebra

end IndistinguishabilityClasses

section Prod

/-- A `SigmaAlgebra` structure on the product of two measurable spaces. -/
@[instance_reducible]
def SigmaAlgebra.prod {α β} (m₁ : SigmaAlgebra α) (m₂ : SigmaAlgebra β) :
    SigmaAlgebra (α × β) :=
  m₁.comap Prod.fst ⊔ m₂.comap Prod.snd

instance Prod.instSigmaAlgebra {α β} [m₁ : SigmaAlgebra α] [m₂ : SigmaAlgebra β] :
    SigmaAlgebra (α × β) :=
  m₁.prod m₂

theorem measurable_fst {_ : SigmaAlgebra α} {_ : SigmaAlgebra β} :
    Measurable (Prod.fst : α × β → α) :=
  Measurable.of_comap_le le_sup_left

theorem measurable_snd {_ : SigmaAlgebra α} {_ : SigmaAlgebra β} :
    Measurable (Prod.snd : α × β → β) :=
  Measurable.of_comap_le le_sup_right

variable {m : SigmaAlgebra α} {mβ : SigmaAlgebra β} {mγ : SigmaAlgebra γ}

@[fun_prop]
theorem Measurable.fst {f : α → β × γ} (hf : Measurable f) : Measurable fun a : α => (f a).1 :=
  measurable_fst.comp hf

@[fun_prop]
theorem Measurable.snd {f : α → β × γ} (hf : Measurable f) : Measurable fun a : α => (f a).2 :=
  measurable_snd.comp hf

theorem Measurable.prod {f : α → β × γ} (hf₁ : Measurable fun a => (f a).1)
    (hf₂ : Measurable fun a => (f a).2) : Measurable f :=
  Measurable.of_le_map <|
    sup_le
      (by
        rw [SigmaAlgebra.comap_le_iff_le_map, SigmaAlgebra.map_comp]
        exact hf₁)
      (by
        rw [SigmaAlgebra.comap_le_iff_le_map, SigmaAlgebra.map_comp]
        exact hf₂)

@[fun_prop]
theorem Measurable.prodMk {β γ} {_ : SigmaAlgebra β} {_ : SigmaAlgebra γ} {f : α → β}
    {g : α → γ} (hf : Measurable f) (hg : Measurable g) : Measurable fun a : α => (f a, g a) :=
  Measurable.prod hf hg

@[fun_prop]
theorem Measurable.prodMap [SigmaAlgebra δ] {f : α → β} {g : γ → δ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (Prod.map f g) :=
  (hf.comp measurable_fst).prodMk (hg.comp measurable_snd)

theorem measurable_prodMk_left {x : α} : Measurable (@Prod.mk _ β x) :=
  measurable_const.prodMk measurable_id

theorem measurable_prodMk_right {y : β} : Measurable fun x : α => (x, y) :=
  measurable_id.prodMk measurable_const

@[fun_prop]
theorem measurable_diag : @Measurable α (α × α) m (m.prod m) Function.diag :=
  measurable_id.prodMk measurable_id

theorem measurable_diag' {m'} (h : m' ≤ m) : @Measurable α (α × α) m (m.prod m') Function.diag :=
  measurable_id.prodMk (measurable_id'' h)

theorem Measurable.of_uncurry_left {f : α → β → γ} (hf : Measurable (uncurry f)) {x : α} :
    Measurable (f x) :=
  hf.comp measurable_prodMk_left

theorem Measurable.of_uncurry_right {f : α → β → γ} (hf : Measurable (uncurry f)) {y : β} :
    Measurable fun x => f x y :=
  hf.comp measurable_prodMk_right

theorem measurable_fun_prod {f : α → β × γ} :
    Measurable f ↔ (Measurable fun a => (f a).1) ∧ Measurable fun a => (f a).2 :=
  ⟨fun hf => ⟨measurable_fst.comp hf, measurable_snd.comp hf⟩, fun h => Measurable.prod h.1 h.2⟩

@[fun_prop]
theorem measurable_swap : Measurable (Prod.swap : α × β → β × α) :=
  Measurable.prod measurable_snd measurable_fst

theorem measurable_swap_iff {_ : SigmaAlgebra γ} {f : α × β → γ} :
    Measurable (f ∘ Prod.swap) ↔ Measurable f :=
  ⟨fun hf => hf.comp measurable_swap, fun hf => hf.comp measurable_swap⟩

@[measurability]
protected theorem MeasurableSet.prod {s : Set α} {t : Set β} (hs : MeasurableSet s)
    (ht : MeasurableSet t) : MeasurableSet (s ×ˢ t) :=
  MeasurableSet.inter (measurable_fst hs) (measurable_snd ht)

theorem measurableSet_prod_of_nonempty {s : Set α} {t : Set β} (h : (s ×ˢ t).Nonempty) :
    MeasurableSet (s ×ˢ t) ↔ MeasurableSet s ∧ MeasurableSet t := by
  rcases h with ⟨⟨x, y⟩, hx, hy⟩
  refine ⟨fun hst => ?_, fun h => h.1.prod h.2⟩
  have : MeasurableSet ((fun x => (x, y)) ⁻¹' s ×ˢ t) := measurable_prodMk_right hst
  have : MeasurableSet (Prod.mk x ⁻¹' s ×ˢ t) := measurable_prodMk_left hst
  simp_all

theorem measurableSet_prod {s : Set α} {t : Set β} :
    MeasurableSet (s ×ˢ t) ↔ MeasurableSet s ∧ MeasurableSet t ∨ s = ∅ ∨ t = ∅ := by
  rcases (s ×ˢ t).eq_empty_or_nonempty with h | h
  · simp [h, prod_eq_empty_iff.mp h]
  · simp [← not_nonempty_iff_eq_empty, prod_nonempty_iff.mp h, measurableSet_prod_of_nonempty h]

theorem measurableSet_swap_iff {s : Set (α × β)} :
    MeasurableSet (Prod.swap ⁻¹' s) ↔ MeasurableSet s :=
  ⟨fun hs => measurable_swap hs, fun hs => measurable_swap hs⟩

instance Prod.instMeasurableSingletonClass
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α × β) :=
  ⟨fun ⟨a, b⟩ => @singleton_prod_singleton _ _ a b ▸ .prod (.singleton a) (.singleton b)⟩

/-- See `measurable_from_prod_countable_left` for a version where we assume that singletons are
measurable instead of reasoning about indistinguishability classes. -/
theorem measurable_from_prod_countable_left' [Countable β] {f : α × β → γ}
    (hf : ∀ y, Measurable fun x => f (x, y))
    (h'f : ∀ y y' x, y' ∈ (inferInstance : SigmaAlgebra β).indistinguishabilityClass y →
      f (x, y') = f (x, y)) : Measurable f := fun s hs => by
  have : f ⁻¹' s = ⋃ y, ((fun x => f (x, y)) ⁻¹' s) ×ˢ
      (inferInstance : SigmaAlgebra β).indistinguishabilityClass y := by
    ext1 ⟨x, y⟩
    simp only [mem_preimage, mem_iUnion, mem_prod]
    refine ⟨fun h ↦ ⟨y, h, SigmaAlgebra.self_mem_indistinguishabilityClass _ y⟩, ?_⟩
    rintro ⟨y', hy's, hy'⟩
    rwa [h'f y' y x hy']
  rw [this]
  exact MeasurableSet.iUnion (fun y : β ↦ MeasurableSet.prod (hf y hs)
    (SigmaAlgebra.indistinguishabilityClass_mem_of_countable y))

/-- See `measurable_from_prod_countable_right` for a version where we assume that singletons are
measurable instead of reasoning about indistinguishability classes. -/
lemma measurable_from_prod_countable_right' [Countable α] {f : α × β → γ}
    (hf : ∀ x, Measurable fun y => f (x, y))
    (h'f : ∀ x x' y, x' ∈ (inferInstance : SigmaAlgebra α).indistinguishabilityClass x →
      f (x', y) = f (x, y)) : Measurable f := by
  change Measurable ((fun p ↦ f (p.2, p.1)) ∘ Prod.swap)
  exact (measurable_from_prod_countable_left' hf h'f).comp measurable_swap

/-- For the version where the first space in the product is countable,
see `measurable_from_prod_countable_right`. -/
theorem measurable_from_prod_countable_left [Countable β] [MeasurableSingletonClass β]
    {f : α × β → γ} (hf : ∀ y, Measurable fun x => f (x, y)) :
    Measurable f :=
  measurable_from_prod_countable_left' hf (by simp +contextual)

/-- For the version where the second space in the product is countable,
see `measurable_from_prod_countable_left`. -/
lemma measurable_from_prod_countable_right [Countable α] [MeasurableSingletonClass α]
    {f : α × β → γ} (hf : ∀ x, Measurable fun y => f (x, y)) : Measurable f :=
  measurable_from_prod_countable_right' hf (by simp +contextual)

/-- A piecewise function on countably many pieces is measurable if all the data is measurable. -/
theorem Measurable.find {_ : SigmaAlgebra α} {f : ℕ → α → β} {p : ℕ → α → Prop}
    [∀ n, DecidablePred (p n)] (hf : ∀ n, Measurable (f n)) (hp : ∀ n, MeasurableSet { x | p n x })
    (h : ∀ x, ∃ n, p n x) : Measurable fun x => f (Nat.find (h x)) x :=
  have : Measurable fun p : α × ℕ => f p.2 p.1 := measurable_from_prod_countable_left fun n => hf n
  this.comp (Measurable.prodMk measurable_id (measurable_find h hp))

/-- Let `t i` be a countable covering of a set `T` by measurable sets. Let `f i : t i → β` be a
family of functions that agree on the intersections `t i ∩ t j`. Then the function
`Set.iUnionLift t f _ _ : T → β`, defined as `f i ⟨x, hx⟩` for `hx : x ∈ t i`, is measurable. -/
theorem measurable_iUnionLift [Countable ι] {t : ι → Set α} {f : ∀ i, t i → β}
    (htf : ∀ (i j) (x : α) (hxi : x ∈ t i) (hxj : x ∈ t j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩)
    {T : Set α} (hT : T ⊆ ⋃ i, t i) (htm : ∀ i, MeasurableSet (t i)) (hfm : ∀ i, Measurable (f i)) :
    Measurable (iUnionLift t f htf T hT) := fun s hs => by
  rw [preimage_iUnionLift]
  exact MeasurableSet.preimage
    (MeasurableSet.iUnion fun i => MeasurableSet.image_inclusion _ (htm _) (hfm i hs))
    (measurable_inclusion _)

/-- Let `t i` be a countable covering of `α` by measurable sets. Let `f i : t i → β` be a family of
functions that agree on the intersections `t i ∩ t j`. Then the function `Set.liftCover t f _ _`,
defined as `f i ⟨x, hx⟩` for `hx : x ∈ t i`, is measurable. -/
theorem measurable_liftCover [Countable ι] (t : ι → Set α) (htm : ∀ i, MeasurableSet (t i))
    (f : ∀ i, t i → β) (hfm : ∀ i, Measurable (f i))
    (hf : ∀ (i j) (x : α) (hxi : x ∈ t i) (hxj : x ∈ t j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩)
    (htU : ⋃ i, t i = univ) :
    Measurable (liftCover t f hf htU) := fun s hs => by
  rw [preimage_liftCover]
  exact MeasurableSet.iUnion fun i => MeasurableSet.subtype_image (htm i) <| hfm i hs

/-- Let `t i` be a nonempty countable family of measurable sets in `α`. Let `g i : α → β` be a
family of measurable functions such that `g i` agrees with `g j` on `t i ∩ t j`. Then there exists
a measurable function `f : α → β` that agrees with each `g i` on `t i`.

We only need the assumption `[Nonempty ι]` to prove `[Nonempty (α → β)]`. -/
theorem exists_measurable_piecewise {ι} [Countable ι] [Nonempty ι] (t : ι → Set α)
    (t_meas : ∀ n, MeasurableSet (t n)) (g : ι → α → β) (hg : ∀ n, Measurable (g n))
    (ht : Pairwise fun i j => EqOn (g i) (g j) (t i ∩ t j)) :
    ∃ f : α → β, Measurable f ∧ ∀ n, EqOn f (g n) (t n) := by
  inhabit ι
  set g' : (i : ι) → t i → β := fun i => g i ∘ (↑)
  -- see https://github.com/leanprover-community/mathlib4/issues/2184
  have ht' : ∀ (i j) (x : α) (hxi : x ∈ t i) (hxj : x ∈ t j), g' i ⟨x, hxi⟩ = g' j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    rcases eq_or_ne i j with rfl | hij
    · rfl
    · exact ht hij ⟨hxi, hxj⟩
  set f : (⋃ i, t i) → β := iUnionLift t g' ht' _ Subset.rfl
  have hfm : Measurable f := measurable_iUnionLift _ _ t_meas
    (fun i => (hg i).comp measurable_subtype_coe)
  classical
    refine ⟨fun x => if hx : x ∈ ⋃ i, t i then f ⟨x, hx⟩ else g default x,
      hfm.dite ((hg default).comp measurable_subtype_coe) (.iUnion t_meas), fun i x hx => ?_⟩
    simp only [dite_eq_left (mem_iUnion.2 ⟨i, hx⟩)]
    exact iUnionLift_of_mem ⟨x, mem_iUnion.2 ⟨i, hx⟩⟩ hx

end Prod

section Pi

variable {X : δ → Type*} [SigmaAlgebra α]

instance SigmaAlgebra.pi [m : ∀ a, SigmaAlgebra (X a)] : SigmaAlgebra (∀ a, X a) :=
  ⨆ a, (m a).comap fun b => b a

variable [∀ a, SigmaAlgebra (X a)] [SigmaAlgebra γ]

theorem measurable_pi_iff {g : α → ∀ a, X a} : Measurable g ↔ ∀ a, Measurable fun x => g x a := by
  simp_rw [measurable_iff_comap_le, SigmaAlgebra.pi, SigmaAlgebra.comap_iSup,
    SigmaAlgebra.comap_comp, Function.comp_def, iSup_le_iff]

@[fun_prop]
theorem measurable_pi_apply (a : δ) : Measurable fun f : ∀ a, X a => f a :=
  measurable_pi_iff.1 measurable_id a

theorem SigmaAlgebra.comap_le_comap_pi {g : (a : δ) → β → X a} (a : δ) :
    .comap (g a) inferInstance ≤ pi.comap (fun b c ↦ g c b) := by
  simpa only [pi, comap_iSup] using le_iSup_of_le a <| by measurability

theorem Measurable.eval {a : δ} {g : α → ∀ a, X a} (hg : Measurable g) :
    Measurable fun x => g x a :=
  (measurable_pi_apply a).comp hg

@[fun_prop]
theorem Measurable.of_eval {f : α → ∀ a, X a} (hf : ∀ a, Measurable fun c => f c a) :
    Measurable f :=
  measurable_pi_iff.mpr hf

@[deprecated (since := "2026-08-20")] alias measurable_pi_lambda := Measurable.of_eval

lemma SigmaAlgebra.comap_process_pi (X : (a : δ) → β → X a) :
    SigmaAlgebra.comap (fun b a ↦ X a b) inferInstance =
      ⨆ a, SigmaAlgebra.comap (X a) inferInstance := by
  simp_rw [SigmaAlgebra.pi, SigmaAlgebra.comap_iSup, SigmaAlgebra.comap_comp]
  rfl

/-- The function `(f, x) ↦ update f a x : (Π a, X a) × X a → Π a, X a` is measurable. -/
@[fun_prop]
theorem measurable_update' {a : δ} [DecidableEq δ] :
    Measurable (fun p : (∀ i, X i) × X a ↦ update p.1 a p.2) := by
  rw [measurable_pi_iff]
  intro j
  dsimp [update]
  split_ifs with h
  · subst h
    dsimp
    exact measurable_snd
  · exact measurable_pi_iff.1 measurable_fst _

@[fun_prop]
theorem measurable_uniqueElim [Unique δ] :
    Measurable (uniqueElim : X (default : δ) → ∀ i, X i) := by
  simp_rw [measurable_pi_iff, Unique.forall_iff, uniqueElim_default]; exact measurable_id

@[fun_prop]
theorem measurable_updateFinset' [DecidableEq δ] {s : Finset δ} :
    Measurable (fun p : (Π i, X i) × (Π i : s, X i) ↦ updateFinset p.1 s p.2) := by
  simp only [updateFinset, measurable_pi_iff]
  intro i
  by_cases h : i ∈ s <;> simp [h, Measurable.eval, measurable_fst, measurable_snd]

@[fun_prop]
theorem measurable_updateFinset [DecidableEq δ] {s : Finset δ} {x : Π i, X i} :
    Measurable (updateFinset x s) :=
  measurable_updateFinset'.comp measurable_prodMk_left

@[fun_prop]
theorem measurable_updateFinset_left [DecidableEq δ] {s : Finset δ} {x : Π i : s, X i} :
    Measurable (updateFinset · s x) :=
  measurable_updateFinset'.comp measurable_prodMk_right

/-- The function `update f a : X a → Π a, X a` is always measurable.
  This doesn't require `f` to be measurable.
  This should not be confused with the statement that `update f a x` is measurable. -/
@[fun_prop]
theorem measurable_update (f : ∀ a : δ, X a) {a : δ} [DecidableEq δ] : Measurable (update f a) :=
  measurable_update'.comp measurable_prodMk_left

@[fun_prop]
theorem measurable_update_left {a : δ} [DecidableEq δ] {x : X a} :
    Measurable (update · a x) :=
  measurable_update'.comp measurable_prodMk_right

@[fun_prop]
theorem Set.measurable_restrict (s : Set δ) : Measurable (s.domRestrict (π := X)) :=
  .of_eval fun _ ↦ measurable_pi_apply _

@[fun_prop]
theorem Set.measurable_restrict₂ {s t : Set δ} (hst : s ⊆ t) :
    Measurable (domRestrict₂ (π := X) hst) :=
  .of_eval fun _ ↦ measurable_pi_apply _

@[fun_prop]
theorem Finset.measurable_restrict (s : Finset δ) : Measurable (s.restrict (π := X)) :=
  .of_eval fun _ ↦ measurable_pi_apply _

@[fun_prop]
theorem Finset.measurable_restrict₂ {s t : Finset δ} (hst : s ⊆ t) :
    Measurable (Finset.restrict₂ (π := X) hst) :=
  .of_eval fun _ ↦ measurable_pi_apply _

@[fun_prop]
theorem Set.measurable_restrict_apply (s : Set α) {f : α → γ} (hf : Measurable f) :
    Measurable (s.domRestrict f) := hf.comp measurable_subtype_coe

@[fun_prop]
theorem Set.measurable_restrict₂_apply {s t : Set α} (hst : s ⊆ t)
    {f : t → γ} (hf : Measurable f) :
    Measurable (domRestrict₂ (π := fun _ ↦ γ) hst f) := hf.comp (measurable_inclusion hst)

@[fun_prop]
theorem Finset.measurable_restrict_apply (s : Finset α) {f : α → γ} (hf : Measurable f) :
    Measurable (s.restrict f) := hf.comp measurable_subtype_coe

@[fun_prop]
theorem Finset.measurable_restrict₂_apply {s t : Finset α} (hst : s ⊆ t)
    {f : t → γ} (hf : Measurable f) :
    Measurable (restrict₂ (π := fun _ ↦ γ) hst f) := hf.comp (measurable_inclusion hst)

variable (X) in
theorem measurable_eq_mp {i i' : δ} (h : i = i') : Measurable (congr_arg X h).mp := by
  cases h
  exact measurable_id

variable (X) in
theorem Measurable.eq_mp {β} [SigmaAlgebra β] {i i' : δ} (h : i = i') {f : β → X i}
    (hf : Measurable f) : Measurable fun x => (congr_arg X h).mp (f x) :=
  (measurable_eq_mp X h).comp hf

@[fun_prop]
theorem measurable_piCongrLeft (f : δ' ≃ δ) : Measurable (Equiv.piCongrLeft X f) := by
  rw [measurable_pi_iff]
  intro i
  simp_rw [Equiv.piCongrLeft_apply_eq_cast]
  exact Measurable.eq_mp X (f.apply_symm_apply i) <| measurable_pi_apply <| f.symm i

/- Even though we cannot use projection notation, we still keep a dot to be consistent with similar
lemmas, like `MeasurableSet.prod`. -/
@[measurability]
protected theorem MeasurableSet.pi {s : Set δ} {t : ∀ i : δ, Set (X i)} (hs : s.Countable)
    (ht : ∀ i ∈ s, MeasurableSet (t i)) : MeasurableSet (s.pi t) := by
  rw [pi_def]
  exact MeasurableSet.biInter hs fun i hi => measurable_pi_apply _ (ht i hi)

protected theorem MeasurableSet.univ_pi [Countable δ] {t : ∀ i : δ, Set (X i)}
    (ht : ∀ i, MeasurableSet (t i)) : MeasurableSet (pi univ t) :=
  MeasurableSet.pi (to_countable _) fun i _ => ht i

theorem MeasurableSet.univ_pi' [Countable δ] {t : ∀ i : δ, Set (X i)}
    (ht : ∀ i, MeasurableSet (t i)) : MeasurableSet {f : ∀ i : δ, X i | ∀ i : δ, f i ∈ t i} :=
  (MeasurableSet.univ_pi ht).congr (by grind)

theorem measurableSet_pi_of_nonempty {s : Set δ} {t : ∀ i, Set (X i)} (hs : s.Countable)
    (h : (pi s t).Nonempty) : MeasurableSet (pi s t) ↔ ∀ i ∈ s, MeasurableSet (t i) := by
  classical
    rcases h with ⟨f, hf⟩
    refine ⟨fun hst i hi => ?_, MeasurableSet.pi hs⟩
    convert! measurable_update f (a := i) hst
    rw [update_preimage_pi hi]
    exact fun j hj _ => hf j hj

theorem measurableSet_pi {s : Set δ} {t : ∀ i, Set (X i)} (hs : s.Countable) :
    MeasurableSet (pi s t) ↔ (∀ i ∈ s, MeasurableSet (t i)) ∨ pi s t = ∅ := by
  rcases (pi s t).eq_empty_or_nonempty with h | h
  · simp [h]
  · simp [measurableSet_pi_of_nonempty hs, h, ← not_nonempty_iff_eq_empty]

instance Pi.instMeasurableSingletonClass [Countable δ] [∀ a, MeasurableSingletonClass (X a)] :
    MeasurableSingletonClass (∀ a, X a) :=
  ⟨fun f => univ_pi_singleton f ▸ MeasurableSet.univ_pi fun t => measurableSet_singleton (f t)⟩

variable (X)

@[fun_prop]
theorem measurable_piEquivPiSubtypeProd_symm (p : δ → Prop) [DecidablePred p] :
    Measurable (Equiv.piEquivPiSubtypeProd p X).symm := by
  refine measurable_pi_iff.2 fun j => ?_
  by_cases hj : p j
  · simp only [hj, dite_eq_left, Equiv.piEquivPiSubtypeProd_symm_apply]
    have : Measurable fun (f : ∀ i : { x // p x }, X i.1) => f ⟨j, hj⟩ :=
      measurable_pi_apply (X := fun i : {x // p x} => X i.1) ⟨j, hj⟩
    exact Measurable.comp this measurable_fst
  · simp only [hj, Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_right, not_false_iff]
    have : Measurable fun (f : ∀ i : { x // ¬p x }, X i.1) => f ⟨j, hj⟩ :=
      measurable_pi_apply (X := fun i : {x // ¬p x} => X i.1) ⟨j, hj⟩
    exact Measurable.comp this measurable_snd

@[fun_prop]
theorem measurable_piEquivPiSubtypeProd (p : δ → Prop) [DecidablePred p] :
    Measurable (Equiv.piEquivPiSubtypeProd p X) :=
  (measurable_pi_iff.2 fun _ => measurable_pi_apply _).prodMk
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _)

end Pi

instance TProd.instSigmaAlgebra (X : δ → Type*) [∀ i, SigmaAlgebra (X i)] :
    ∀ l : List δ, SigmaAlgebra (List.TProd X l)
  | [] => PUnit.instSigmaAlgebra
  | _::is => @Prod.instSigmaAlgebra _ _ _ (TProd.instSigmaAlgebra X is)

section TProd

open List

variable {X : δ → Type*} [∀ i, SigmaAlgebra (X i)]

theorem measurable_tProd_mk (l : List δ) : Measurable (@TProd.mk δ X l) := by
  induction l with
  | nil => exact measurable_const
  | cons i l ih => exact (measurable_pi_apply i).prodMk ih

set_option backward.isDefEq.respectTransparency false in
theorem measurable_tProd_elim [DecidableEq δ] :
    ∀ {l : List δ} {i : δ} (hi : i ∈ l), Measurable fun v : TProd X l => v.elim hi
  | i::is, j, hj => by
    by_cases hji : j = i
    · subst hji
      simpa using measurable_fst
    · simp only [TProd.elim_of_ne _ hji]
      rw [mem_cons] at hj
      exact (measurable_tProd_elim (hj.resolve_left hji)).comp measurable_snd

theorem measurable_tProd_elim' [DecidableEq δ] {l : List δ} (h : ∀ i, i ∈ l) :
    Measurable (TProd.elim' h : TProd X l → ∀ i, X i) :=
  .of_eval fun i => measurable_tProd_elim (h i)

theorem MeasurableSet.tProd (l : List δ) {s : ∀ i, Set (X i)} (hs : ∀ i, MeasurableSet (s i)) :
    MeasurableSet (Set.tprod l s) := by
  induction l with
  | nil => exact MeasurableSet.univ
  | cons i l ih => exact (hs i).prod ih

end TProd

instance Sum.instSigmaAlgebra {α β} [m₁ : SigmaAlgebra α] [m₂ : SigmaAlgebra β] :
    SigmaAlgebra (α ⊕ β) :=
  m₁.map Sum.inl ⊓ m₂.map Sum.inr

section Sum

@[fun_prop]
theorem measurable_inl [SigmaAlgebra α] [SigmaAlgebra β] : Measurable (@Sum.inl α β) :=
  Measurable.of_le_map inf_le_left

@[fun_prop]
theorem measurable_inr [SigmaAlgebra α] [SigmaAlgebra β] : Measurable (@Sum.inr α β) :=
  Measurable.of_le_map inf_le_right

variable {m : SigmaAlgebra α} {mβ : SigmaAlgebra β}

theorem measurableSet_sum_iff {s : Set (α ⊕ β)} :
    MeasurableSet s ↔ MeasurableSet (Sum.inl ⁻¹' s) ∧ MeasurableSet (Sum.inr ⁻¹' s) :=
  Iff.rfl

theorem measurable_fun_sum {_ : SigmaAlgebra γ} {f : α ⊕ β → γ} (hl : Measurable (f ∘ Sum.inl))
    (hr : Measurable (f ∘ Sum.inr)) : Measurable f :=
  Measurable.of_comap_le <|
    le_inf (SigmaAlgebra.comap_le_iff_le_map.2 <| hl)
      (SigmaAlgebra.comap_le_iff_le_map.2 <| hr)

@[fun_prop]
theorem Measurable.sumElim {_ : SigmaAlgebra γ} {f : α → γ} {g : β → γ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (Sum.elim f g) :=
  measurable_fun_sum hf hg

theorem Measurable.sumMap {_ : SigmaAlgebra γ} {_ : SigmaAlgebra δ} {f : α → β} {g : γ → δ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (Sum.map f g) :=
  (measurable_inl.comp hf).sumElim (measurable_inr.comp hg)

@[simp] theorem measurableSet_inl_image {s : Set α} :
    MeasurableSet (Sum.inl '' s : Set (α ⊕ β)) ↔ MeasurableSet s := by
  simp [measurableSet_sum_iff, Sum.inl_injective.preimage_image]

alias ⟨_, MeasurableSet.inl_image⟩ := measurableSet_inl_image

@[simp] theorem measurableSet_inr_image {s : Set β} :
    MeasurableSet (Sum.inr '' s : Set (α ⊕ β)) ↔ MeasurableSet s := by
  simp [measurableSet_sum_iff, Sum.inr_injective.preimage_image]

alias ⟨_, MeasurableSet.inr_image⟩ := measurableSet_inr_image

theorem measurableSet_range_inl [SigmaAlgebra α] :
    MeasurableSet (range Sum.inl : Set (α ⊕ β)) := by
  rw [← image_univ]
  exact MeasurableSet.univ.inl_image

theorem measurableSet_range_inr [SigmaAlgebra α] :
    MeasurableSet (range Sum.inr : Set (α ⊕ β)) := by
  rw [← image_univ]
  exact MeasurableSet.univ.inr_image

end Sum

instance Sigma.instSigmaAlgebra {α} {β : α → Type*} [m : ∀ a, SigmaAlgebra (β a)] :
    SigmaAlgebra (Sigma β) :=
  ⨅ a, (m a).map (Sigma.mk a)

section prop
variable [SigmaAlgebra α] {p q : α → Prop}

@[simp] theorem measurableSet_setOfPred : MeasurableSet {a | p a} ↔ Measurable p :=
  ⟨fun h ↦ measurable_to_prop <| by simpa only [preimage_singleton_true], fun h => by
    change {a | p a} ∈ (inferInstance : SigmaAlgebra α)
    simpa using h (measurableSet_singleton True)⟩

@[deprecated (since := "2026-07-09")] alias measurableSet_setOf := measurableSet_setOfPred

@[simp] theorem measurable_mem : Measurable (· ∈ s) ↔ MeasurableSet s :=
  measurableSet_setOfPred.symm

alias ⟨_, Measurable.setOf⟩ := measurableSet_setOfPred

@[fun_prop]
alias ⟨_, MeasurableSet.mem⟩ := measurable_mem

@[fun_prop]
lemma Measurable.not (hp : Measurable p) : Measurable (¬ p ·) :=
  measurableSet_setOfPred.1 hp.setOf.compl

@[fun_prop]
lemma Measurable.and (hp : Measurable p) (hq : Measurable q) : Measurable fun a ↦ p a ∧ q a :=
  measurableSet_setOfPred.1 <| hp.setOf.inter hq.setOf

@[fun_prop]
lemma Measurable.or (hp : Measurable p) (hq : Measurable q) : Measurable fun a ↦ p a ∨ q a :=
  measurableSet_setOfPred.1 <| hp.setOf.union hq.setOf

@[fun_prop]
lemma Measurable.imp (hp : Measurable p) (hq : Measurable q) : Measurable fun a ↦ p a → q a :=
  measurableSet_setOfPred.1 <| hp.setOf.himp hq.setOf

@[fun_prop]
lemma Measurable.iff (hp : Measurable p) (hq : Measurable q) : Measurable fun a ↦ p a ↔ q a :=
  measurableSet_setOfPred.1 <| by
    simp_rw [iff_iff_implies_and_implies]; exact hq.setOf.bihimp hp.setOf

@[fun_prop]
lemma Measurable.forall [Countable ι] {p : ι → α → Prop} (hp : ∀ i, Measurable (p i)) :
    Measurable fun a ↦ ∀ i, p i a :=
  measurableSet_setOfPred.1 <| by
    rw [ofPred_forall]; exact MeasurableSet.iInter fun i ↦ (hp i).setOf

@[fun_prop]
lemma Measurable.exists [Countable ι] {p : ι → α → Prop} (hp : ∀ i, Measurable (p i)) :
    Measurable fun a ↦ ∃ i, p i a :=
  measurableSet_setOfPred.1 <| by
    rw [ofPred_exists]; exact MeasurableSet.iUnion fun i ↦ (hp i).setOf

end prop

@[fun_prop]
lemma Measurable.eq_const {_ : SigmaAlgebra α} [SigmaAlgebra β] [MeasurableSingletonClass β]
    {f : α → β} (hf : Measurable f) (a : β) : Measurable fun x => f x = a :=
  measurableSet_setOfPred.mp (measurableSet_eq.preimage hf)

@[fun_prop]
lemma Measurable.const_eq {_ : SigmaAlgebra α} [SigmaAlgebra β] [MeasurableSingletonClass β]
    {f : α → β} (hf : Measurable f) (a : β) : Measurable fun x => a = f x := by
  conv => enter [1, x]; rw [eq_comm]
  exact .eq_const hf a

section Set
variable [SigmaAlgebra β] {g : β → Set α}

/-- This instance is useful when talking about Bernoulli sequences of random variables or binomial
random graphs. -/
instance Set.instSigmaAlgebra : SigmaAlgebra (Set α) :=
  inferInstanceAs <| SigmaAlgebra (α → Prop)

instance Set.instMeasurableSingletonClass [Countable α] : MeasurableSingletonClass (Set α) :=
  inferInstanceAs <| MeasurableSingletonClass (α → Prop)

@[simp, fun_prop] lemma measurable_setOfPred :
    Measurable fun p : α → Prop ↦ {a | p a} := measurable_id

@[deprecated (since := "2026-07-09")]
alias measurable_setOf := measurable_setOfPred

lemma measurable_set_iff : Measurable g ↔ ∀ a, Measurable fun x ↦ a ∈ g x := measurable_pi_iff

@[fun_prop]
lemma measurable_set_mem (a : α) : Measurable fun s : Set α ↦ a ∈ s := measurable_pi_apply _

lemma measurable_set_notMem (a : α) : Measurable fun s : Set α ↦ a ∉ s :=
  (Measurable.of_discrete (f := Not)).comp <| measurable_set_mem a

lemma measurableSet_mem (a : α) : MeasurableSet {s : Set α | a ∈ s} :=
  measurableSet_setOfPred.2 <| measurable_set_mem _

lemma measurableSet_notMem (a : α) : MeasurableSet {s : Set α | a ∉ s} :=
  measurableSet_setOfPred.2 <| measurable_set_notMem _

lemma measurable_compl : Measurable ((·ᶜ) : Set α → Set α) :=
  measurable_set_iff.2 fun _ ↦ measurable_set_notMem _

variable [Countable α]

lemma MeasurableSet.setOfPred_finite : MeasurableSet {s : Set α | s.Finite} :=
  Countable.ofPred_finite.measurableSet

@[deprecated (since := "2026-07-09")]
alias MeasurableSet.setOf_finite := MeasurableSet.setOfPred_finite

lemma MeasurableSet.setOfPred_infinite : MeasurableSet {s : Set α | s.Infinite} :=
  .setOfPred_finite |> .compl

@[deprecated (since := "2026-07-09")]
alias MeasurableSet.setOf_infinite := MeasurableSet.setOfPred_infinite

lemma MeasurableSet.sep_finite {S : Set (Set α)} (hS : MeasurableSet S) :
    MeasurableSet {s ∈ S | s.Finite} :=
  hS.inter .setOfPred_finite

lemma MeasurableSet.sep_infinite {S : Set (Set α)} (hS : MeasurableSet S) :
    MeasurableSet {s ∈ S | s.Infinite} :=
  hS.inter .setOfPred_infinite

@[fun_prop]
protected lemma Measurable.subset {s t : β → Set α} (hs : Measurable s) (hs : Measurable t) :
    Measurable fun a ↦ s a ⊆ t a :=
  .forall fun i ↦ .imp (by fun_prop) (by fun_prop)

end Set

section Finset
variable [SigmaAlgebra β] {g : β → Finset α}

/-- We give `Finset α` the measurable structure inherited from `Set α`.

This is the smallest sigma-algebra generated by `(a ∈ ·)` for all `a : α`.
See `measurable_finset_iff`. -/
instance Finset.instSigmaAlgebra : SigmaAlgebra (Finset α) :=
  .comap SetLike.coe inferInstance

lemma measurable_finset_iff_measurable_set : Measurable g ↔ Measurable (fun x ↦ (g x : Set α)) :=
  measurable_comap_iff

lemma measurable_finset_iff : Measurable g ↔ ∀ a, Measurable (a ∈ g ·) := by
  rw [measurable_finset_iff_measurable_set, measurable_set_iff]; rfl

lemma measurableSet_finset_iff (S : Set (Finset α)) : MeasurableSet S ↔
    ∃ S' : Set (Set α), MeasurableSet S' ∧ { s : Finset α | ↑s ∈ S'} = S :=
  SigmaAlgebra.mem_comap

@[fun_prop]
lemma measurable_finset_mem (a : α) : Measurable fun s : Finset α ↦ a ∈ s :=
  (measurable_set_mem a).comp (comap_measurable _)

lemma measurable_finset_notMem (a : α) : Measurable fun s : Finset α ↦ a ∉ s :=
  (measurable_set_notMem a).comp (comap_measurable _)

lemma measurableSet_mem_finset (a : α) : MeasurableSet {s : Finset α | a ∈ s} :=
  measurableSet_setOfPred.2 <| measurable_finset_mem _

lemma measurableSet_notMem_finset (a : α) : MeasurableSet {s : Finset α | a ∉ s} :=
  measurableSet_setOfPred.2 <| measurable_finset_notMem _

variable [Countable α]

instance Finset.instMeasurableSingletonClass : MeasurableSingletonClass (Finset α) :=
  .mk fun S ↦ (measurableSet_finset_iff _).mpr ⟨{↑S}, by simp, by ext; simp⟩

end Finset

section curry

variable {ι : Type*}

section Function

variable {κ X : Type*} [SigmaAlgebra X]

@[fun_prop]
lemma measurable_curry : Measurable (@curry ι κ X) :=
  .of_eval fun _ ↦ .of_eval fun _ ↦ measurable_pi_apply _

-- This cannot be tagged with `fun_prop` because `fun_prop` can see through `Function.uncurry`.
lemma measurable_uncurry : Measurable (@uncurry ι κ X) := by fun_prop

@[fun_prop]
lemma measurable_equivCurry : Measurable (Equiv.curry ι κ X) := measurable_curry

@[fun_prop]
lemma measurable_equivCurry_symm : Measurable (Equiv.curry ι κ X).symm := measurable_uncurry

end Function

section Sigma

variable {κ : ι → Type*} {X : (i : ι) → κ i → Type*} [∀ i j, SigmaAlgebra (X i j)]

@[fun_prop]
lemma measurable_sigmaCurry : Measurable (Sigma.curry (γ := X)) :=
    .of_eval fun _ ↦ .of_eval fun _ ↦ measurable_pi_apply _

@[fun_prop]
lemma measurable_sigmaUncurry : Measurable (Sigma.uncurry (γ := X)) := by
  refine .of_eval fun _ ↦ ?_
  simp only [Sigma.uncurry]
  fun_prop

@[fun_prop]
lemma measurable_piCurry : Measurable (Equiv.piCurry X) := measurable_sigmaCurry

@[fun_prop]
lemma measurable_piCurry_symm : Measurable (Equiv.piCurry X).symm := measurable_sigmaUncurry

end Sigma

end curry

variable (α) in
/-- Typeclass for a measurable space `α` for which the diagonal of `α × α` is measurable. -/
class MeasurableEq [SigmaAlgebra α] where
  measurableSet_diagonal : MeasurableSet (diagonal α)

export MeasurableEq (measurableSet_diagonal)

attribute [measurability] measurableSet_diagonal

theorem measurableSet_eq_fun {m : SigmaAlgebra α} [SigmaAlgebra β] [MeasurableEq β]
    {f g : α → β} (hf : Measurable f) (hg : Measurable g) : MeasurableSet {x | f x = g x} :=
  measurableSet_diagonal.preimage (hf.prodMk hg)

@[fun_prop]
theorem Measurable.eq {m : SigmaAlgebra α} [SigmaAlgebra β] [MeasurableEq β]
    {f g : α → β} (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x = g x :=
  measurableSet_setOfPred.mp (measurableSet_eq_fun hf hg)

instance [SigmaAlgebra α] [MeasurableEq α] : MeasurableSingletonClass α := by
  constructor
  simp_rw [← ofPred_eq_eq_singleton, measurableSet_setOfPred]
  measurability

instance [SigmaAlgebra α] [MeasurableSingletonClass α] [Countable α] : MeasurableEq α := by
  constructor
  simp_rw [← Set.range_diag, Set.range_eq_iUnion]
  measurability
