/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.FunProp.Attr
public import Mathlib.Tactic.Measurability

/-!
# Sigma-algebras and measurable functions

This file defines σ-algebras on fixed types and measurable functions.

`SigmaAlgebra α` bundles a family of subsets of `α` together with the proof that it is a
σ-algebra. Equipping a type `α` with an instance `[SigmaAlgebra α]` makes it a measurable space in
the usual typeclass style. `MeasurableSpace` packages the carrier and its σ-algebra as one object
when the whole pair must be passed as data. A function between equipped types is measurable if the
preimage of each measurable subset is measurable.

σ-algebras on a fixed set `α` form a complete lattice. Here we order
σ-algebras by writing `m₁ ≤ m₂` if every set which is `m₁`-measurable is
also `m₂`-measurable (that is, `m₁` is a subset of `m₂`). In particular, any
collection of subsets of `α` generates a smallest σ-algebra which
contains all of them.

## References

* <https://en.wikipedia.org/wiki/Measurable_space>
* <https://en.wikipedia.org/wiki/Sigma-algebra>
* <https://en.wikipedia.org/wiki/Dynkin_system>

## Tags

measurable space, σ-algebra, measurable function
-/

@[expose] public section

assert_not_exists Covariant MonoidWithZero

open Set Function

variable {α β γ δ : Type*} {ι : Sort*} {s t u : Set α}

/-- A family of subsets is a σ-algebra if it contains the empty set and is closed under
complements and countable unions. -/
structure IsSigmaAlgebra (C : Set (Set α)) : Prop where
  /-- A σ-algebra contains the empty set. -/
  empty_mem : ∅ ∈ C
  /-- A σ-algebra is closed under complements. -/
  compl_mem : ∀ ⦃s⦄, s ∈ C → sᶜ ∈ C
  /-- A σ-algebra is closed under countable unions. -/
  iUnion_mem_nat : ∀ f : ℕ → Set α, (∀ i, f i ∈ C) → ⋃ i, f i ∈ C

namespace IsSigmaAlgebra

/-- A σ-algebra is closed under countable indexed unions. -/
theorem iUnion_mem {C : Set (Set α)} (hC : IsSigmaAlgebra C) [Countable ι]
    {s : ι → Set α} (hs : ∀ i, s i ∈ C) : ⋃ i, s i ∈ C := by
  cases isEmpty_or_nonempty ι
  · simpa using hC.empty_mem
  · obtain ⟨f, hf⟩ := exists_surjective_nat ι
    rw [← iUnion_congr_of_surjective _ hf (fun _ ↦ rfl)]
    exact hC.iUnion_mem_nat _ fun n ↦ hs (f n)

/-- A σ-algebra contains the whole space. -/
theorem univ_mem {C : Set (Set α)} (hC : IsSigmaAlgebra C) : univ ∈ C := by
  simpa using hC.compl_mem hC.empty_mem

/-- Membership in a σ-algebra is invariant under complements. -/
theorem compl_mem_iff {C : Set (Set α)} (hC : IsSigmaAlgebra C) : sᶜ ∈ C ↔ s ∈ C :=
  ⟨fun hs ↦ by simpa using hC.compl_mem hs, fun hs ↦ hC.compl_mem hs⟩

/-- A σ-algebra is closed under countable indexed intersections. -/
theorem iInter_mem {C : Set (Set α)} (hC : IsSigmaAlgebra C) [Countable ι]
    {s : ι → Set α} (hs : ∀ i, s i ∈ C) : ⋂ i, s i ∈ C := by
  simpa only [compl_iUnion, compl_compl] using
    hC.compl_mem (hC.iUnion_mem fun i ↦ hC.compl_mem (hs i))

/-- A σ-algebra is closed under unions of countable families. -/
theorem sUnion_mem {C : Set (Set α)} (hC : IsSigmaAlgebra C) {S : Set (Set α)}
    (hS : S.Countable) (hSC : S ⊆ C) : ⋃₀ S ∈ C := by
  let _ := hS.to_subtype
  rw [sUnion_eq_iUnion]
  exact hC.iUnion_mem fun s : S ↦ hSC s.property

/-- A σ-algebra is closed under binary unions. -/
theorem union_mem {C : Set (Set α)} (hC : IsSigmaAlgebra C) {s t : Set α}
    (hs : s ∈ C) (ht : t ∈ C) : s ∪ t ∈ C := by
  rw [union_eq_iUnion]
  exact hC.iUnion_mem (Bool.forall_bool.2 ⟨ht, hs⟩)

/-- A σ-algebra is closed under binary intersections. -/
theorem inter_mem {C : Set (Set α)} (hC : IsSigmaAlgebra C) {s t : Set α}
    (hs : s ∈ C) (ht : t ∈ C) : s ∩ t ∈ C := by
  rw [inter_eq_compl_compl_union_compl]
  exact hC.compl_mem (hC.union_mem (hC.compl_mem hs) (hC.compl_mem ht))

/-- A σ-algebra is closed under set difference. -/
theorem diff_mem {C : Set (Set α)} (hC : IsSigmaAlgebra C) {s t : Set α}
    (hs : s ∈ C) (ht : t ∈ C) : s \ t ∈ C :=
  hC.inter_mem hs (hC.compl_mem ht)

end IsSigmaAlgebra

/-- A bundled σ-algebra of subsets of `α`. The underlying family is available through the
`SetLike` coercion, so `s ∈ 𝓐` means that `s` is measurable with respect to `𝓐`. -/
@[class] structure SigmaAlgebra (α : Type*) where
  /-- The family of measurable subsets. -/
  carrier : Set (Set α)
  /-- The measurable subsets form a σ-algebra. -/
  isSigmaAlgebra : IsSigmaAlgebra carrier

instance : SetLike (SigmaAlgebra α) (Set α) where
  coe := SigmaAlgebra.carrier
  coe_injective m n h := by
    cases m
    cases n
    simp_all

universe u_ms

/-- A measurable space is a carrier type equipped with a σ-algebra.

Use `m : SigmaAlgebra α` when the carrier `α` is already fixed, and `X : MeasurableSpace` when the
carrier together with its σ-algebra must be treated as one object. -/
structure MeasurableSpace : Type (u_ms + 1) where
  /-- Bundle an equipped type as a measurable space. -/
  of ::
  /-- The underlying carrier. -/
  carrier : Type u_ms
  /-- The σ-algebra of measurable subsets of the carrier. -/
  [sigmaAlgebra : SigmaAlgebra carrier]

attribute [instance] MeasurableSpace.sigmaAlgebra

namespace MeasurableSpace

instance : CoeSort MeasurableSpace (Type u_ms) :=
  ⟨carrier⟩

attribute [coe] MeasurableSpace.carrier

@[simp]
theorem coe_of (α : Type u_ms) [SigmaAlgebra α] : (of α : Type u_ms) = α :=
  rfl

@[simp]
theorem of_carrier (X : MeasurableSpace.{u_ms}) : of X = X :=
  rfl

end MeasurableSpace

namespace SigmaAlgebra

/-- The empty set belongs to every σ-algebra. -/
theorem empty_mem (𝓐 : SigmaAlgebra α) : ∅ ∈ 𝓐 :=
  𝓐.isSigmaAlgebra.empty_mem

/-- A σ-algebra is closed under complements. -/
theorem compl_mem (𝓐 : SigmaAlgebra α) {s : Set α} (hs : s ∈ 𝓐) : sᶜ ∈ 𝓐 :=
  𝓐.isSigmaAlgebra.compl_mem hs

/-- A σ-algebra is closed under countable indexed unions. -/
theorem iUnion_mem (𝓐 : SigmaAlgebra α) [Countable ι] {s : ι → Set α} (hs : ∀ i, s i ∈ 𝓐) :
    ⋃ i, s i ∈ 𝓐 :=
  𝓐.isSigmaAlgebra.iUnion_mem hs

/-- A σ-algebra contains the whole space. -/
theorem univ_mem (𝓐 : SigmaAlgebra α) : univ ∈ 𝓐 :=
  𝓐.isSigmaAlgebra.univ_mem

/-- Membership in a σ-algebra is invariant under complements. -/
theorem compl_mem_iff (𝓐 : SigmaAlgebra α) : sᶜ ∈ 𝓐 ↔ s ∈ 𝓐 :=
  𝓐.isSigmaAlgebra.compl_mem_iff

/-- A σ-algebra is closed under countable indexed intersections. -/
theorem iInter_mem (𝓐 : SigmaAlgebra α) [Countable ι] {s : ι → Set α} (hs : ∀ i, s i ∈ 𝓐) :
    ⋂ i, s i ∈ 𝓐 :=
  𝓐.isSigmaAlgebra.iInter_mem hs

/-- A σ-algebra is closed under unions of countable families. -/
theorem sUnion_mem (𝓐 : SigmaAlgebra α) {S : Set (Set α)} (hS : S.Countable) (hS𝓐 : S ⊆ 𝓐) :
    ⋃₀ S ∈ 𝓐 :=
  𝓐.isSigmaAlgebra.sUnion_mem hS hS𝓐

/-- A σ-algebra is closed under unions indexed by a countable set. -/
theorem biUnion_mem (𝓐 : SigmaAlgebra α) {f : β → Set α} {s : Set β} (hs : s.Countable)
    (hf : ∀ b ∈ s, f b ∈ 𝓐) : ⋃ b ∈ s, f b ∈ 𝓐 := by
  rw [biUnion_eq_iUnion]
  let _ := hs.to_subtype
  exact 𝓐.iUnion_mem (by simpa using hf)

/-- A σ-algebra is closed under intersections indexed by a countable set. -/
theorem biInter_mem (𝓐 : SigmaAlgebra α) {f : β → Set α} {s : Set β} (hs : s.Countable)
    (hf : ∀ b ∈ s, f b ∈ 𝓐) : ⋂ b ∈ s, f b ∈ 𝓐 := by
  apply (𝓐.compl_mem_iff).mp
  rw [compl_iInter₂]
  exact 𝓐.biUnion_mem hs fun b hb ↦ 𝓐.compl_mem (hf b hb)

/-- A σ-algebra is closed under binary unions. -/
theorem union_mem (𝓐 : SigmaAlgebra α) {s t : Set α} (hs : s ∈ 𝓐) (ht : t ∈ 𝓐) : s ∪ t ∈ 𝓐 :=
  𝓐.isSigmaAlgebra.union_mem hs ht

/-- A σ-algebra is closed under binary intersections. -/
theorem inter_mem (𝓐 : SigmaAlgebra α) {s t : Set α} (hs : s ∈ 𝓐) (ht : t ∈ 𝓐) : s ∩ t ∈ 𝓐 :=
  𝓐.isSigmaAlgebra.inter_mem hs ht

/-- A σ-algebra is closed under set difference. -/
theorem diff_mem (𝓐 : SigmaAlgebra α) {s t : Set α} (hs : s ∈ 𝓐) (ht : t ∈ 𝓐) : s \ t ∈ 𝓐 :=
  𝓐.isSigmaAlgebra.diff_mem hs ht

end SigmaAlgebra

namespace IsSigmaAlgebra

/-- Bundle a family satisfying the σ-algebra axioms. -/
@[instance_reducible]
def toSigmaAlgebra {C : Set (Set α)} (hC : IsSigmaAlgebra C) : SigmaAlgebra α where
  carrier := C
  isSigmaAlgebra := hC

@[simp]
theorem coe_toSigmaAlgebra {C : Set (Set α)} (hC : IsSigmaAlgebra C) :
    (hC.toSigmaAlgebra : Set (Set α)) = C :=
  rfl

end IsSigmaAlgebra

instance [h : SigmaAlgebra α] : SigmaAlgebra αᵒᵈ := h

/-- `MeasurableSet s` means that `s` belongs to the ambient σ-algebra on `α`.

For an explicit `𝓐 : SigmaAlgebra α`, write `s ∈ 𝓐`. When an explicit `MeasurableSet` predicate
head is useful for elaboration, write `MeasurableSet (𝓐 := 𝓐) s`. -/
def MeasurableSet [𝓐 : SigmaAlgebra α] (s : Set α) : Prop :=
  s ∈ 𝓐

theorem measurableSet_iff_mem {𝓐 : SigmaAlgebra α} {s : Set α} :
    MeasurableSet (𝓐 := 𝓐) s ↔ s ∈ 𝓐 :=
  Iff.rfl

section

open scoped symmDiff

@[simp, measurability]
theorem MeasurableSet.empty [SigmaAlgebra α] : MeasurableSet (∅ : Set α) :=
  SigmaAlgebra.empty_mem _

variable {m : SigmaAlgebra α}

@[measurability]
protected theorem MeasurableSet.compl : MeasurableSet s → MeasurableSet sᶜ :=
  SigmaAlgebra.compl_mem _

protected theorem MeasurableSet.of_compl (h : MeasurableSet sᶜ) : MeasurableSet s :=
  compl_compl s ▸ h.compl

@[simp]
theorem MeasurableSet.compl_iff : MeasurableSet sᶜ ↔ MeasurableSet s :=
  ⟨.of_compl, .compl⟩

@[simp, measurability]
protected theorem MeasurableSet.univ : MeasurableSet (univ : Set α) :=
  .of_compl <| by simp

@[nontriviality, measurability]
theorem Subsingleton.measurableSet [Subsingleton α] {s : Set α} : MeasurableSet s :=
  Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s

theorem MeasurableSet.congr {s t : Set α} (hs : MeasurableSet s) (h : s = t) : MeasurableSet t := by
  rwa [← h]

@[measurability]
protected theorem MeasurableSet.iUnion [Countable ι] ⦃f : ι → Set α⦄
    (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) :=
  m.iUnion_mem h

protected theorem MeasurableSet.biUnion {f : β → Set α} {s : Set β} (hs : s.Countable)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b) := by
  rw [biUnion_eq_iUnion]
  have := hs.to_subtype
  exact MeasurableSet.iUnion (by simpa using h)

theorem Set.Finite.measurableSet_biUnion {f : β → Set α} {s : Set β} (hs : s.Finite)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b) :=
  .biUnion hs.countable h

theorem Finset.measurableSet_biUnion {f : β → Set α} (s : Finset β)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b) :=
  s.finite_toSet.measurableSet_biUnion h

protected theorem MeasurableSet.sUnion {s : Set (Set α)} (hs : s.Countable)
    (h : ∀ t ∈ s, MeasurableSet t) : MeasurableSet (⋃₀ s) := by
  rw [sUnion_eq_biUnion]
  exact .biUnion hs h

theorem Set.Finite.measurableSet_sUnion {s : Set (Set α)} (hs : s.Finite)
    (h : ∀ t ∈ s, MeasurableSet t) : MeasurableSet (⋃₀ s) :=
  MeasurableSet.sUnion hs.countable h

@[measurability]
theorem MeasurableSet.iInter [Countable ι] {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) :
    MeasurableSet (⋂ b, f b) :=
  .of_compl <| by rw [compl_iInter]; exact .iUnion fun b => (h b).compl

theorem MeasurableSet.biInter {f : β → Set α} {s : Set β} (hs : s.Countable)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b) :=
  .of_compl <| by rw [compl_iInter₂]; exact .biUnion hs fun b hb => (h b hb).compl

theorem Set.Finite.measurableSet_biInter {f : β → Set α} {s : Set β} (hs : s.Finite)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b) :=
  .biInter hs.countable h

theorem Finset.measurableSet_biInter {f : β → Set α} (s : Finset β)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b) :=
  s.finite_toSet.measurableSet_biInter h

theorem MeasurableSet.sInter {s : Set (Set α)} (hs : s.Countable) (h : ∀ t ∈ s, MeasurableSet t) :
    MeasurableSet (⋂₀ s) := by
  rw [sInter_eq_biInter]
  exact MeasurableSet.biInter hs h

theorem Set.Finite.measurableSet_sInter {s : Set (Set α)} (hs : s.Finite)
    (h : ∀ t ∈ s, MeasurableSet t) : MeasurableSet (⋂₀ s) :=
  MeasurableSet.sInter hs.countable h

@[simp, measurability]
protected theorem MeasurableSet.union {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∪ s₂) := by
  rw [union_eq_iUnion]
  exact .iUnion (Bool.forall_bool.2 ⟨h₂, h₁⟩)

@[simp, measurability]
protected theorem MeasurableSet.inter {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∩ s₂) := by
  rw [inter_eq_compl_compl_union_compl]
  exact (h₁.compl.union h₂.compl).compl

@[simp, measurability]
protected theorem MeasurableSet.diff {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ \ s₂) :=
  h₁.inter h₂.compl

@[simp, measurability]
protected lemma MeasurableSet.himp {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
    MeasurableSet (s₁ ⇨ s₂) := by rw [himp_eq]; exact h₂.union h₁.compl

@[simp, measurability]
protected theorem MeasurableSet.symmDiff {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∆ s₂) :=
  (h₁.diff h₂).union (h₂.diff h₁)

@[simp, measurability]
protected lemma MeasurableSet.bihimp {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ⇔ s₂) := (h₂.himp h₁).inter (h₁.himp h₂)

@[simp, measurability]
protected theorem MeasurableSet.ite {t s₁ s₂ : Set α} (ht : MeasurableSet t)
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) : MeasurableSet (t.ite s₁ s₂) :=
  (h₁.inter ht).union (h₂.diff ht)

open scoped Classical in
theorem MeasurableSet.ite' {s t : Set α} {p : Prop} (hs : p → MeasurableSet s)
    (ht : ¬p → MeasurableSet t) : MeasurableSet (ite p s t) := by
  split_ifs with h
  exacts [hs h, ht h]

@[simp, measurability]
protected theorem MeasurableSet.cond {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) {i : Bool} : MeasurableSet (if i = true then s₁ else s₂) := by
  cases i
  exacts [h₂, h₁]

protected theorem MeasurableSet.const (p : Prop) : MeasurableSet { _a : α | p } := by
  by_cases p <;> simp [*]

protected lemma MeasurableSet.imp {p q : α → Prop}
    (hs : MeasurableSet {x | p x}) (ht : MeasurableSet {x | q x}) :
    MeasurableSet {x | p x → q x} := by
  have h_eq : {x | p x → q x} = {x | p x}ᶜ ∪ {x | q x} := by grind
  rw [h_eq]
  exact hs.compl.union ht

protected lemma MeasurableSet.iff {p q : α → Prop}
    (hs : MeasurableSet {x | p x}) (ht : MeasurableSet {x | q x}) :
    MeasurableSet {x | p x ↔ q x} := by
  have h_eq : {x | p x ↔ q x} = {x | p x → q x} ∩ {x | q x → p x} := by ext; simp; grind
  rw [h_eq]
  exact (hs.imp ht).inter (ht.imp hs)

/-- Every set has a measurable superset. Declare this as local instance as needed. -/
theorem nonempty_measurable_superset (s : Set α) : Nonempty { t // s ⊆ t ∧ MeasurableSet t } :=
  ⟨⟨univ, subset_univ s, MeasurableSet.univ⟩⟩

end

theorem SigmaAlgebra.coe_injective : Injective (fun m : SigmaAlgebra α ↦ (m : Set (Set α))) :=
  SetLike.coe_injective

@[ext]
theorem SigmaAlgebra.ext {m₁ m₂ : SigmaAlgebra α}
    (h : ∀ s : Set α, s ∈ m₁ ↔ s ∈ m₂) : m₁ = m₂ :=
  SetLike.ext h

/-- A typeclass mixin for `SigmaAlgebra`s such that each singleton is measurable. -/
class MeasurableSingletonClass (α : Type*) [SigmaAlgebra α] : Prop where
  /-- A singleton is a measurable set. -/
  measurableSet_singleton : ∀ x, MeasurableSet ({x} : Set α)

export MeasurableSingletonClass (measurableSet_singleton)

@[simp]
lemma MeasurableSet.singleton [SigmaAlgebra α] [MeasurableSingletonClass α] (a : α) :
    MeasurableSet {a} :=
  measurableSet_singleton a

section MeasurableSingletonClass

variable [SigmaAlgebra α] [MeasurableSingletonClass α]

theorem measurableSet_eq {a : α} : MeasurableSet { x | x = a } := .singleton a

@[measurability]
protected theorem MeasurableSet.insert {s : Set α} (hs : MeasurableSet s) (a : α) :
    MeasurableSet (insert a s) :=
  .union (.singleton a) hs

@[simp]
theorem measurableSet_insert {a : α} {s : Set α} :
    MeasurableSet (insert a s) ↔ MeasurableSet s := by
  classical
  exact ⟨fun h =>
    if ha : a ∈ s then by rwa [← insert_eq_of_mem ha]
    else insert_sdiff_self_of_notMem ha ▸ h.diff (.singleton _),
    fun h => h.insert a⟩

theorem Set.Subsingleton.measurableSet {s : Set α} (hs : s.Subsingleton) : MeasurableSet s :=
  hs.induction_on .empty .singleton

theorem Set.Finite.measurableSet {s : Set α} (hs : s.Finite) : MeasurableSet s :=
  Finite.induction_on _ hs .empty fun _ _ hsm => hsm.insert _

@[measurability]
protected theorem Finset.measurableSet (s : Finset α) : MeasurableSet (↑s : Set α) :=
  s.finite_toSet.measurableSet

theorem Set.Countable.measurableSet {s : Set α} (hs : s.Countable) : MeasurableSet s := by
  rw [← biUnion_of_singleton s]
  exact .biUnion hs fun b _ => .singleton b

end MeasurableSingletonClass

namespace SigmaAlgebra

/-! ### First-class measurable sets -/

namespace Element

variable {𝓐 : SigmaAlgebra α}

/-- A point belongs to a first-class measurable set through its underlying subset. -/
instance instMembership : Membership α 𝓐 :=
  ⟨fun A x ↦ x ∈ (A : Set α)⟩

@[simp]
theorem mem_coe (x : α) (A : 𝓐) : x ∈ (A : Set α) ↔ x ∈ A :=
  Iff.rfl

instance instEmptyCollection : EmptyCollection 𝓐 :=
  ⟨⟨∅, 𝓐.empty_mem⟩⟩

@[simp]
theorem coe_empty : ((∅ : 𝓐) : Set α) = ∅ :=
  rfl

instance instInsert [@MeasurableSingletonClass α 𝓐] : Insert α 𝓐 where
  insert x A := ⟨insert x (A : Set α), by
    rw [insert_eq]
    exact 𝓐.union_mem (@measurableSet_singleton α 𝓐 _ x) A.property⟩

@[simp]
theorem coe_insert [@MeasurableSingletonClass α 𝓐] (x : α) (A : 𝓐) :
    ((insert x A : 𝓐) : Set α) = insert x (A : Set α) :=
  rfl

instance instSingleton [@MeasurableSingletonClass α 𝓐] : Singleton α 𝓐 :=
  ⟨fun x ↦ ⟨{x}, @measurableSet_singleton α 𝓐 _ x⟩⟩

@[simp]
theorem coe_singleton [@MeasurableSingletonClass α 𝓐] (x : α) :
    (({x} : 𝓐) : Set α) = {x} :=
  rfl

instance instLawfulSingleton [@MeasurableSingletonClass α 𝓐] : LawfulSingleton α 𝓐 :=
  ⟨fun _ ↦ Subtype.ext <| insert_empty_eq _⟩

instance instCompl : Compl 𝓐 :=
  ⟨fun A ↦ ⟨(A : Set α)ᶜ, 𝓐.compl_mem A.property⟩⟩

@[simp]
theorem coe_compl (A : 𝓐) : ((Aᶜ : 𝓐) : Set α) = (A : Set α)ᶜ :=
  rfl

instance instUnion : Union 𝓐 :=
  ⟨fun A B ↦ ⟨(A : Set α) ∪ (B : Set α), 𝓐.union_mem A.property B.property⟩⟩

@[simp]
theorem coe_union (A B : 𝓐) : ((A ∪ B : 𝓐) : Set α) = (A : Set α) ∪ (B : Set α) :=
  rfl

instance instMax : Max 𝓐 :=
  ⟨(· ∪ ·)⟩

@[simp]
theorem sup_eq_union (A B : 𝓐) : A ⊔ B = A ∪ B :=
  rfl

instance instInter : Inter 𝓐 :=
  ⟨fun A B ↦ ⟨(A : Set α) ∩ (B : Set α), 𝓐.inter_mem A.property B.property⟩⟩

@[simp]
theorem coe_inter (A B : 𝓐) : ((A ∩ B : 𝓐) : Set α) = (A : Set α) ∩ (B : Set α) :=
  rfl

instance instMin : Min 𝓐 :=
  ⟨(· ∩ ·)⟩

@[simp]
theorem inf_eq_inter (A B : 𝓐) : A ⊓ B = A ∩ B :=
  rfl

instance instSDiff : SDiff 𝓐 :=
  ⟨fun A B ↦ ⟨(A : Set α) \ (B : Set α), 𝓐.diff_mem A.property B.property⟩⟩

@[simp]
theorem coe_sdiff (A B : 𝓐) : ((A \ B : 𝓐) : Set α) = (A : Set α) \ (B : Set α) :=
  rfl

noncomputable instance instHImp : HImp 𝓐 where
  himp A B := ⟨(A : Set α) ⇨ (B : Set α), by
    rw [himp_eq]
    exact 𝓐.union_mem B.property (𝓐.compl_mem A.property)⟩

@[simp]
theorem coe_himp (A B : 𝓐) : ((A ⇨ B : 𝓐) : Set α) = (A : Set α) ⇨ (B : Set α) :=
  rfl

instance instBot : Bot 𝓐 :=
  ⟨∅⟩

@[simp]
theorem coe_bot : ((⊥ : 𝓐) : Set α) = ⊥ :=
  rfl

instance instTop : Top 𝓐 :=
  ⟨⟨Set.univ, 𝓐.univ_mem⟩⟩

@[simp]
theorem coe_top : ((⊤ : 𝓐) : Set α) = ⊤ :=
  rfl

noncomputable instance instBooleanAlgebra : BooleanAlgebra 𝓐 :=
  Subtype.coe_injective.booleanAlgebra _ .rfl .rfl coe_union coe_inter coe_top coe_bot coe_compl
    coe_sdiff coe_himp

end Element

/-- The union of a countable family of first-class measurable sets. -/
def countableUnion (𝓐 : SigmaAlgebra α) [Countable ι] (A : ι → 𝓐) : 𝓐 :=
  ⟨⋃ i, (A i : Set α), 𝓐.iUnion_mem fun i ↦ (A i).property⟩

@[simp]
theorem coe_countableUnion (𝓐 : SigmaAlgebra α) [Countable ι] (A : ι → 𝓐) :
    (𝓐.countableUnion A : Set α) = ⋃ i, (A i : Set α) :=
  rfl

/-- The intersection of a countable family of first-class measurable sets. -/
def countableInter (𝓐 : SigmaAlgebra α) [Countable ι] (A : ι → 𝓐) : 𝓐 :=
  ⟨⋂ i, (A i : Set α), 𝓐.iInter_mem fun i ↦ (A i).property⟩

@[simp]
theorem coe_countableInter (𝓐 : SigmaAlgebra α) [Countable ι] (A : ι → 𝓐) :
    (𝓐.countableInter A : Set α) = ⋂ i, (A i : Set α) :=
  rfl

/-- Copy of a `SigmaAlgebra` with a definitionally new membership predicate equal to the old one.
Useful to fix
definitional equalities. -/
@[instance_reducible]
protected def copy (m : SigmaAlgebra α) (p : Set α → Prop) (h : ∀ s, p s ↔ s ∈ m) :
    SigmaAlgebra α where
  carrier := p
  isSigmaAlgebra :=
    { empty_mem := (h ∅).2 m.empty_mem
      compl_mem := by
        intro s hs
        exact (h _).2 (m.compl_mem ((h _).1 hs))
      iUnion_mem_nat := fun s hs ↦ (h _).2 (m.iUnion_mem fun n ↦ (h _).1 (hs n)) }

lemma mem_copy {m : SigmaAlgebra α} {p : Set α → Prop}
    (h : ∀ s, p s ↔ s ∈ m) {s} : s ∈ m.copy p h ↔ p s :=
  Iff.rfl

lemma copy_eq {m : SigmaAlgebra α} {p : Set α → Prop} (h : ∀ s, p s ↔ s ∈ m) :
    m.copy p h = m :=
  ext h

section CompleteLattice

instance : PartialOrder (SigmaAlgebra α) :=
  PartialOrder.ofSetLike (SigmaAlgebra α) (Set α)

theorem le_def {α} {a b : SigmaAlgebra α} : a ≤ b ↔ (a : Set (Set α)) ⊆ b :=
  Iff.rfl

/-- The smallest σ-algebra containing a collection `s` of basic sets -/
inductive GenerateMeasurable (s : Set (Set α)) : Set α → Prop
  | protected basic : ∀ u ∈ s, GenerateMeasurable s u
  | protected empty : GenerateMeasurable s ∅
  | protected compl : ∀ t, GenerateMeasurable s t → GenerateMeasurable s tᶜ
  | protected iUnion : ∀ f : ℕ → Set α, (∀ n, GenerateMeasurable s (f n)) →
      GenerateMeasurable s (⋃ i, f i)

/-- Construct the smallest σ-algebra containing a collection of basic sets. -/
@[instance_reducible]
def generateFrom (s : Set (Set α)) : SigmaAlgebra α where
  carrier := GenerateMeasurable s
  isSigmaAlgebra :=
    { empty_mem := .empty
      compl_mem := .compl
      iUnion_mem_nat := .iUnion }

theorem mem_generateFrom {C : Set (Set α)} {s : Set α} (hs : s ∈ C) : s ∈ generateFrom C :=
  GenerateMeasurable.basic s hs

@[elab_as_elim]
theorem generateFrom_induction (C : Set (Set α))
    (p : ∀ s : Set α, s ∈ generateFrom C → Prop)
    (basic : ∀ s (hs : s ∈ C), p s (mem_generateFrom hs))
    (empty : p ∅ (generateFrom C).empty_mem)
    (compl : ∀ s hs, p s hs → p sᶜ ((generateFrom C).compl_mem hs))
    (iUnion : ∀ (s : ℕ → Set α) (hs : ∀ n, s n ∈ generateFrom C),
      (∀ n, p (s n) (hs n)) → p (⋃ n, s n) ((generateFrom C).iUnion_mem hs))
    {s : Set α} (hs : s ∈ generateFrom C) : p s hs := by
  induction hs with
  | basic s hs => exact basic s hs
  | empty => exact empty
  | compl s _ ih => exact compl s _ ih
  | iUnion s _ ih => exact iUnion s _ ih

theorem generateFrom_le {C : Set (Set α)} {m : SigmaAlgebra α} (h : C ⊆ m) :
    generateFrom C ≤ m :=
  fun _ hs ↦ by
    induction hs with
    | basic s hs => exact h hs
    | empty => exact m.empty_mem
    | compl _ _ ht => exact m.compl_mem ht
    | iUnion _ _ ht => exact m.iUnion_mem ht

theorem generateFrom_le_iff {C : Set (Set α)} (m : SigmaAlgebra α) :
    generateFrom C ≤ m ↔ C ⊆ m :=
  ⟨fun h _ hs ↦ h (mem_generateFrom hs), generateFrom_le⟩

@[simp]
theorem generateFrom_self (m : SigmaAlgebra α) : generateFrom (m : Set (Set α)) = m :=
  le_antisymm (generateFrom_le Subset.rfl) fun _ hs ↦ mem_generateFrom hs

theorem forall_generateFrom_mem_iff_mem_iff {S : Set (Set α)} {x y : α} :
    (∀ s ∈ generateFrom S, x ∈ s ↔ y ∈ s) ↔ (∀ s ∈ S, x ∈ s ↔ y ∈ s) := by
  refine ⟨fun H s hs ↦ H s (mem_generateFrom hs), fun H s hs ↦ ?_⟩
  induction hs using generateFrom_induction with
  | basic s hs => exact H s hs
  | empty => rfl
  | compl _ _ ih => exact Iff.not ih
  | iUnion s _ ih => simp only [mem_iUnion, ih]

@[instance_reducible]
def ofGenerateFromFixedPoint (g : Set (Set α))
    (hg : (generateFrom g : Set (Set α)) = g) : SigmaAlgebra α :=
  (generateFrom g).copy (· ∈ g) <| Set.ext_iff.1 hg.symm

theorem ofGenerateFromFixedPoint_eq {s : Set (Set α)}
    {hs : (generateFrom s : Set (Set α)) = s} :
    ofGenerateFromFixedPoint s hs = generateFrom s :=
  copy_eq _

/-- Generating a σ-algebra is left adjoint to taking its underlying family of sets. -/
def giGenerateFrom : GaloisInsertion (@generateFrom α) (fun m ↦ (m : Set (Set α))) where
  gc _ := generateFrom_le_iff
  le_l_u _ _ h := mem_generateFrom h
  choice g hg := ofGenerateFromFixedPoint g <| le_antisymm hg <| (generateFrom_le_iff _).1 le_rfl
  choice_eq _ _ := ofGenerateFromFixedPoint_eq

instance : CompleteLattice (SigmaAlgebra α) :=
  giGenerateFrom.liftCompleteLattice

@[simp]
theorem coe_top : ((⊤ : SigmaAlgebra α) : Set (Set α)) = Set.univ :=
  (@giGenerateFrom α).gc.u_top

@[simp]
theorem coe_inf (m₁ m₂ : SigmaAlgebra α) :
    ((m₁ ⊓ m₂ : SigmaAlgebra α) : Set (Set α)) = (m₁ : Set (Set α)) ∩ m₂ :=
  (@giGenerateFrom α).gc.u_inf

@[simp]
theorem coe_sInf (s : Set (SigmaAlgebra α)) :
    ((sInf s : SigmaAlgebra α) : Set (Set α)) = ⨅ m ∈ s, (m : Set (Set α)) :=
  (@giGenerateFrom α).gc.u_sInf

@[simp]
theorem coe_iInf (m : ι → SigmaAlgebra α) :
    ((⨅ i, m i : SigmaAlgebra α) : Set (Set α)) = ⋂ i, (m i : Set (Set α)) :=
  (@giGenerateFrom α).gc.u_iInf

instance : Inhabited (SigmaAlgebra α) := ⟨⊤⟩

@[gcongr, mono]
theorem generateFrom_mono {s t : Set (Set α)} (h : s ⊆ t) : generateFrom s ≤ generateFrom t :=
  giGenerateFrom.gc.monotone_l h

theorem generateFrom_sup_generateFrom {s t : Set (Set α)} :
    generateFrom s ⊔ generateFrom t = generateFrom (s ∪ t) :=
  (@giGenerateFrom α).gc.l_sup.symm

lemma iSup_generateFrom (s : ι → Set (Set α)) :
    ⨆ i, generateFrom (s i) = generateFrom (⋃ i, s i) :=
  (@SigmaAlgebra.giGenerateFrom α).gc.l_iSup.symm

@[simp]
lemma generateFrom_empty : generateFrom (∅ : Set (Set α)) = ⊥ :=
  le_bot_iff.mp (generateFrom_le (by simp))

theorem generateFrom_singleton_empty : generateFrom {∅} = (⊥ : SigmaAlgebra α) :=
  bot_unique <| generateFrom_le <| by
    intro s hs
    have : s = ∅ := by simpa using hs
    subst this
    exact (⊥ : SigmaAlgebra α).empty_mem

theorem generateFrom_singleton_univ : generateFrom {Set.univ} = (⊥ : SigmaAlgebra α) :=
  bot_unique <| generateFrom_le <| by
    intro s hs
    have : s = univ := by simpa using hs
    subst this
    exact (⊥ : SigmaAlgebra α).univ_mem

@[simp]
theorem generateFrom_insert_univ (S : Set (Set α)) :
    generateFrom (insert Set.univ S) = generateFrom S := by
  rw [insert_eq, ← generateFrom_sup_generateFrom, generateFrom_singleton_univ, bot_sup_eq]

@[simp]
theorem generateFrom_insert_empty (S : Set (Set α)) :
    generateFrom (insert ∅ S) = generateFrom S := by
  rw [insert_eq, ← generateFrom_sup_generateFrom, generateFrom_singleton_empty, bot_sup_eq]

theorem mem_bot_iff {s : Set α} : s ∈ (⊥ : SigmaAlgebra α) ↔ s = ∅ ∨ s = univ :=
  let b : SigmaAlgebra α :=
    { carrier := {s | s = ∅ ∨ s = univ}
      isSigmaAlgebra :=
        { empty_mem := Or.inl rfl
          compl_mem := by simp +contextual [or_imp]
          iUnion_mem_nat := fun _ hf => sUnion_mem_empty_univ (forall_mem_range.2 hf) } }
  have : b = ⊥ :=
    bot_unique fun _ hs =>
      hs.elim (fun s => s.symm ▸ (⊥ : SigmaAlgebra α).empty_mem) fun s =>
        s.symm ▸ (⊥ : SigmaAlgebra α).univ_mem
  this ▸ Iff.rfl

@[simp, measurability] theorem mem_top {s : Set α} : s ∈ (⊤ : SigmaAlgebra α) := by
  change s ∈ ((⊤ : SigmaAlgebra α) : Set (Set α))
  rw [coe_top]
  trivial

@[simp]
-- The `m₁` parameter gets filled in by typeclass instance synthesis (for some reason...)
-- so we have to order it *after* `m₂`. Otherwise `simp` can't apply this lemma.
theorem mem_inf {m₂ m₁ : SigmaAlgebra α} {s : Set α} :
    s ∈ m₁ ⊓ m₂ ↔ s ∈ m₁ ∧ s ∈ m₂ := by
  change s ∈ ((m₁ ⊓ m₂ : SigmaAlgebra α) : Set (Set α)) ↔ _
  rw [coe_inf]
  rfl

@[simp]
theorem mem_sInf {ms : Set (SigmaAlgebra α)} {s : Set α} :
    s ∈ sInf ms ↔ ∀ m ∈ ms, s ∈ m := by
  change s ∈ ((sInf ms : SigmaAlgebra α) : Set (Set α)) ↔ _
  rw [coe_sInf]
  simp

theorem mem_iInf {ι} {m : ι → SigmaAlgebra α} {s : Set α} :
    s ∈ iInf m ↔ ∀ i, s ∈ m i := by
  rw [iInf, mem_sInf, forall_mem_range]

theorem sup_eq_generateFrom (m₁ m₂ : SigmaAlgebra α) :
    m₁ ⊔ m₂ = generateFrom ((m₁ : Set (Set α)) ∪ m₂) :=
  ((@giGenerateFrom α).l_sup_u m₁ m₂).symm

theorem sSup_eq_generateFrom (ms : Set (SigmaAlgebra α)) :
    sSup ms = generateFrom (⋃₀ ((fun m : SigmaAlgebra α ↦ (m : Set (Set α))) '' ms)) := by
  rw [← Set.sSup_eq_sUnion]
  exact ((@giGenerateFrom α).l_sSup_u_image ms).symm

theorem iSup_eq_generateFrom (m : ι → SigmaAlgebra α) :
    ⨆ i, m i = generateFrom (⋃ i, (m i : Set (Set α))) :=
  ((@giGenerateFrom α).l_iSup_u m).symm

theorem mem_iSup_iff {m : ι → SigmaAlgebra α} {s : Set α} :
    s ∈ ⨆ i, m i ↔ s ∈ generateFrom (⋃ i, (m i : Set (Set α))) := by
  rw [iSup_eq_generateFrom]

end CompleteLattice

end SigmaAlgebra

/-- A function `f` between measurable spaces is measurable if the preimage of every
  measurable set is measurable. -/
@[fun_prop, wikidata Q516776]
def Measurable [𝓐 : SigmaAlgebra α] [𝓑 : SigmaAlgebra β] (f : α → β) : Prop :=
  ∀ ⦃s : Set β⦄, s ∈ 𝓑 → f ⁻¹' s ∈ 𝓐

theorem measurable_iff_preimage_mem {𝓐 : SigmaAlgebra α} {𝓑 : SigmaAlgebra β} {f : α → β} :
    @Measurable α β 𝓐 𝓑 f ↔ ∀ ⦃s : Set β⦄, s ∈ 𝓑 → f ⁻¹' s ∈ 𝓐 :=
  Iff.rfl

add_aesop_rules safe tactic
  (rule_sets := [Measurable])
  (index := [target @Measurable ..])
  (by fun_prop (disch := measurability))

namespace MeasureTheory

set_option quotPrecheck false in
/-- Notation for `Measurable` with respect to a non-standard σ-algebra in the domain. -/
scoped notation "Measurable[" 𝓐 "]" => @Measurable _ _ 𝓐 _
/-- Notation for `Measurable` with respect to a non-standard σ-algebra in the domain and codomain.
-/
scoped notation "Measurable[" 𝓐 ", " 𝓑 "]" => @Measurable _ _ 𝓐 𝓑

end MeasureTheory

open scoped MeasureTheory

section MeasurableFunctions

theorem measurable_id {_ : SigmaAlgebra α} : Measurable (@id α) := fun _ => id

@[fun_prop]
theorem measurable_id' {_ : SigmaAlgebra α} : Measurable fun a : α => a := measurable_id

-- Allow `to_fun` to eta-expand `g ∘ f`. Ideally, `Function.comp_def` would be a global pull lemma
-- instead, which is not supported yet: see https://github.com/leanprover-community/mathlib4/issues/40183.
attribute [local push ←] Function.comp_def
@[to_fun]
protected theorem Measurable.comp {_ : SigmaAlgebra α} {_ : SigmaAlgebra β}
    {_ : SigmaAlgebra γ} {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) :
    Measurable (g ∘ f) :=
  fun _ h => hf (hg h)

attribute [fun_prop] Measurable.fun_comp

@[simp, fun_prop]
theorem measurable_const {_ : SigmaAlgebra α} {_ : SigmaAlgebra β} {a : α} :
    Measurable fun _ : β => a := fun s _ => MeasurableSet.const (a ∈ s)

@[fun_prop]
theorem Measurable.le {α} {𝓐 𝓐₀ : SigmaAlgebra α} {_ : SigmaAlgebra β} (h𝓐 : 𝓐 ≤ 𝓐₀)
    {f : α → β} (hf : Measurable[𝓐] f) : Measurable[𝓐₀] f := fun _ hs => h𝓐 (hf hs)

end MeasurableFunctions

/-- A typeclass mixin for `SigmaAlgebra`s such that all sets are measurable. -/
class DiscreteSigmaAlgebra (α : Type*) [SigmaAlgebra α] : Prop where
  /-- Do not use this. Use `MeasurableSet.of_discrete` instead. -/
  forall_measurableSet : ∀ s : Set α, MeasurableSet s

instance : @DiscreteSigmaAlgebra α ⊤ :=
  @DiscreteSigmaAlgebra.mk _ (_) fun _ ↦ SigmaAlgebra.mem_top

-- See note [lower instance priority]
instance (priority := 100) MeasurableSingletonClass.toDiscreteSigmaAlgebra [SigmaAlgebra α]
    [MeasurableSingletonClass α] [Countable α] : DiscreteSigmaAlgebra α where
  forall_measurableSet _ := (Set.to_countable _).measurableSet

section DiscreteSigmaAlgebra
variable [SigmaAlgebra α] [SigmaAlgebra β] [DiscreteSigmaAlgebra α] {s : Set α} {f : α → β}

@[measurability] lemma MeasurableSet.of_discrete : MeasurableSet s :=
  DiscreteSigmaAlgebra.forall_measurableSet _

@[fun_prop] lemma Measurable.of_discrete : Measurable f := fun _ _ ↦ MeasurableSet.of_discrete

/-- Warning: Creates a typeclass loop with `MeasurableSingletonClass.toDiscreteSigmaAlgebra`.
To be monitored. -/
-- See note [lower instance priority]
instance (priority := 100) DiscreteSigmaAlgebra.toMeasurableSingletonClass :
    MeasurableSingletonClass α where
  measurableSet_singleton _ := .of_discrete

end DiscreteSigmaAlgebra
