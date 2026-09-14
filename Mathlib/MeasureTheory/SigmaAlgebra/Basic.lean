/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Data.Int.Cast.Pi
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.MeasureTheory.SigmaAlgebra.Defs
public import Mathlib.Order.SupClosed

/-!
# Sigma-algebras and measurable functions

This file provides properties of measurable spaces and the functions and isomorphisms between them.
The definition of a measurable space is in `Mathlib/MeasureTheory/SigmaAlgebra/Defs.lean`.

A measurable space is a set equipped with a σ-algebra, a collection of subsets closed under
complementation and countable union. A function between measurable spaces is measurable if
the preimage of each measurable subset is measurable.

σ-algebras on a fixed set `α` form a complete lattice. Here we order σ-algebras by writing `m₁ ≤ m₂`
if every set which is `m₁`-measurable is also `m₂`-measurable (that is, `m₁` is a subset of `m₂`).
In particular, any collection of subsets of `α` generates a smallest σ-algebra which contains
all of them. A function `f : α → β` induces a Galois connection between the lattices of σ-algebras
on `α` and `β`.

## Implementation notes

Measurability of a function `f : α → β` means directly that the preimage of every member of the
codomain σ-algebra belongs to the domain σ-algebra. The induced `comap`/`map` operations form the
corresponding Galois connection on σ-algebras.

## References

* <https://en.wikipedia.org/wiki/Measurable_space>
* <https://en.wikipedia.org/wiki/Sigma-algebra>
* <https://en.wikipedia.org/wiki/Dynkin_system>

## Tags

measurable space, σ-algebra, measurable function, dynkin system, π-λ theorem, π-system
-/

@[expose] public section

open Set

open scoped MeasureTheory

universe uι

variable {α β γ : Type*} {ι : Sort uι} {s : Set α}

namespace SigmaAlgebra

section Functors

variable {m m₁ m₂ : SigmaAlgebra α} {m' : SigmaAlgebra β} {f : α → β} {g : β → α}

/-- The forward image of a σ-algebra under a function. `map f m` contains the sets
  `s : Set β` whose preimage under `f` is measurable. -/
@[instance_reducible]
protected def map (f : α → β) (m : SigmaAlgebra α) : SigmaAlgebra β where
  carrier := {s | f ⁻¹' s ∈ m}
  isSigmaAlgebra :=
    { empty_mem := m.empty_mem
      compl_mem := by
        intro s hs
        change f ⁻¹' sᶜ ∈ m
        rw [preimage_compl]
        exact m.compl_mem hs
      iUnion_mem_nat := by
        intro s hs
        change f ⁻¹' (⋃ n, s n) ∈ m
        rw [preimage_iUnion]
        exact m.iUnion_mem hs }

lemma mem_map {s : Set β} : s ∈ m.map f ↔ f ⁻¹' s ∈ m :=
  Iff.rfl

@[simp]
theorem map_id : m.map id = m :=
  SigmaAlgebra.ext fun s ↦ by change id ⁻¹' s ∈ m ↔ s ∈ m; simp

@[simp]
theorem map_comp {f : α → β} {g : β → γ} : (m.map f).map g = m.map (g ∘ f) :=
  SigmaAlgebra.ext fun s ↦ by
    change f ⁻¹' (g ⁻¹' s) ∈ m ↔ (g ∘ f) ⁻¹' s ∈ m
    rfl

/-- The reverse image of a σ-algebra under a function. `comap f m` contains the sets
  `s : Set α` such that `s` is the `f`-preimage of a measurable set in `β`. -/
@[instance_reducible]
protected def comap (f : α → β) (m : SigmaAlgebra β) : SigmaAlgebra α where
  carrier := {s | ∃ s' ∈ m, f ⁻¹' s' = s}
  isSigmaAlgebra :=
    { empty_mem := ⟨∅, m.empty_mem, rfl⟩
      compl_mem := fun _ ⟨s', h₁, h₂⟩ ↦ ⟨s'ᶜ, m.compl_mem h₁, h₂ ▸ rfl⟩
      iUnion_mem_nat := fun s hs ↦
        let ⟨s', hs'⟩ := Classical.axiom_of_choice hs
        ⟨⋃ i, s' i, m.iUnion_mem fun i ↦ (hs' i).1, by simp [hs']⟩ }

lemma mem_comap {m : SigmaAlgebra β} :
    s ∈ m.comap f ↔ ∃ s' ∈ m, f ⁻¹' s' = s :=
  Iff.rfl

theorem comap_eq_generateFrom (m : SigmaAlgebra β) (f : α → β) :
    m.comap f = generateFrom { t | ∃ s ∈ m, f ⁻¹' s = t } := by
  change m.comap f = generateFrom (m.comap f : Set (Set α))
  exact (generateFrom_self _).symm

@[simp]
theorem comap_id : m.comap id = m :=
  SigmaAlgebra.ext fun s => ⟨fun ⟨_, hs', h⟩ => h ▸ hs', fun h => ⟨s, h, rfl⟩⟩

@[simp]
theorem comap_comp {f : β → α} {g : γ → β} : (m.comap f).comap g = m.comap (f ∘ g) :=
  SigmaAlgebra.ext fun _ =>
    ⟨fun ⟨_, ⟨u, h, hu⟩, ht⟩ => ⟨u, h, ht ▸ hu ▸ rfl⟩, fun ⟨t, h, ht⟩ => ⟨f ⁻¹' t, ⟨_, h, rfl⟩, ht⟩⟩

theorem comap_le_iff_le_map {f : α → β} : m'.comap f ≤ m ↔ m' ≤ m.map f :=
  ⟨fun h _s hs ↦ h ⟨_, hs, rfl⟩, fun h _s ⟨_t, ht, heq⟩ ↦ heq ▸ h ht⟩

theorem gc_comap_map (f : α → β) :
    GaloisConnection (SigmaAlgebra.comap f) (SigmaAlgebra.map f) := fun _ _ =>
  comap_le_iff_le_map

theorem map_mono (h : m₁ ≤ m₂) : m₁.map f ≤ m₂.map f :=
  (gc_comap_map f).monotone_u h

@[gcongr]
theorem monotone_map : Monotone (SigmaAlgebra.map f) := fun _ _ => map_mono

theorem comap_mono (h : m₁ ≤ m₂) : m₁.comap g ≤ m₂.comap g :=
  (gc_comap_map g).monotone_l h

@[gcongr]
theorem monotone_comap : Monotone (SigmaAlgebra.comap g) := fun _ _ h => comap_mono h

@[simp]
theorem comap_bot : (⊥ : SigmaAlgebra α).comap g = ⊥ :=
  (gc_comap_map g).l_bot

@[simp]
theorem comap_sup : (m₁ ⊔ m₂).comap g = m₁.comap g ⊔ m₂.comap g :=
  (gc_comap_map g).l_sup

@[simp]
theorem comap_iSup {m : ι → SigmaAlgebra α} : (⨆ i, m i).comap g = ⨆ i, (m i).comap g :=
  (gc_comap_map g).l_iSup

@[simp]
theorem map_top : (⊤ : SigmaAlgebra α).map f = ⊤ :=
  (gc_comap_map f).u_top

@[simp]
theorem map_inf : (m₁ ⊓ m₂).map f = m₁.map f ⊓ m₂.map f :=
  (gc_comap_map f).u_inf

@[simp]
theorem map_iInf {m : ι → SigmaAlgebra α} : (⨅ i, m i).map f = ⨅ i, (m i).map f :=
  (gc_comap_map f).u_iInf

theorem comap_map_le : (m.map f).comap f ≤ m :=
  (gc_comap_map f).l_u_le _

theorem le_map_comap : m ≤ (m.comap g).map g :=
  (gc_comap_map g).le_u_l _

theorem map_comap_eq_of_surjective (hg : Function.Surjective g) : (m.comap g).map g = m := by
  refine le_antisymm (fun S hS => ?_) le_map_comap
  change ∃ T ∈ m, g ⁻¹' T = g ⁻¹' S at hS
  aesop

end Functors

@[simp] theorem map_const {m} (b : β) : SigmaAlgebra.map (fun _a : α ↦ b) m = ⊤ :=
  eq_top_iff.2 <| fun s _ ↦ by
    change (fun _a : α ↦ b) ⁻¹' s ∈ m
    by_cases h : b ∈ s <;> simp [h, m.empty_mem, m.univ_mem]

@[simp] theorem comap_const {m} (b : β) : SigmaAlgebra.comap (fun _a : α => b) m = ⊥ :=
  eq_bot_iff.2 <| by
    rintro _ ⟨s, -, rfl⟩
    by_cases h : b ∈ s
    · simpa [h] using (SigmaAlgebra.univ_mem (⊥ : SigmaAlgebra α))
    · simpa [h] using (SigmaAlgebra.empty_mem (⊥ : SigmaAlgebra α))

theorem comap_generateFrom {f : α → β} {s : Set (Set β)} :
    (generateFrom s).comap f = generateFrom (preimage f '' s) :=
  le_antisymm
    (comap_le_iff_le_map.2 <|
      generateFrom_le fun _t hts ↦ by
        change f ⁻¹' _t ∈ generateFrom (preimage f '' s)
        exact GenerateMeasurable.basic _ <| mem_image_of_mem _ hts)
    (generateFrom_le fun _t ⟨u, hu, Eq⟩ ↦ by
      change ∃ v ∈ generateFrom s, f ⁻¹' v = _t
      exact Eq ▸ ⟨u, GenerateMeasurable.basic _ hu, rfl⟩)

end SigmaAlgebra

section MeasurableFunctions

open SigmaAlgebra

theorem measurable_iff_le_map {m₁ : SigmaAlgebra α} {m₂ : SigmaAlgebra β} {f : α → β} :
    Measurable f ↔ m₂ ≤ m₁.map f := by
    change (∀ {t : Set β}, t ∈ m₂ → f ⁻¹' t ∈ m₁) ↔
      ∀ {t : Set β}, t ∈ m₂ → f ⁻¹' t ∈ m₁
    rfl

alias ⟨Measurable.le_map, Measurable.of_le_map⟩ := measurable_iff_le_map

theorem measurable_iff_comap_le {m₁ : SigmaAlgebra α} {m₂ : SigmaAlgebra β} {f : α → β} :
    Measurable f ↔ m₂.comap f ≤ m₁ :=
  comap_le_iff_le_map.symm

alias ⟨Measurable.comap_le, Measurable.of_comap_le⟩ := measurable_iff_comap_le

/-- If `g = h ∘ f`, then the sigma-algebra generated by `g` is
smaller than the one generated by `f`. -/
lemma SigmaAlgebra.comap_le_comap_of_eq_comp {mβ : SigmaAlgebra β} {mγ : SigmaAlgebra γ}
    {f : α → β} {g : α → γ} (h : β → γ) (mh : Measurable h) (heq : g = h ∘ f) :
    mγ.comap g ≤ mβ.comap f := by
  rw [heq, ← SigmaAlgebra.comap_comp]
  exact SigmaAlgebra.comap_mono mh.comap_le

theorem comap_measurable {m : SigmaAlgebra β} (f : α → β) : Measurable[m.comap f] f :=
  fun s hs => ⟨s, hs, rfl⟩

lemma measurable_comap_iff {mα : SigmaAlgebra α} {mγ : SigmaAlgebra γ}
    {f : α → β} {g : β → γ} : Measurable[mα, mγ.comap g] f ↔ Measurable (g ∘ f) := by
  simp [measurable_iff_comap_le]

lemma measurable_comap_iff_right {mβ : SigmaAlgebra β} {mγ : SigmaAlgebra γ} {g : α → β}
    {f : β → γ} (hg : Function.Surjective g) : Measurable f ↔ Measurable[mβ.comap g] (f ∘ g) := by
  rw [measurable_iff_le_map, measurable_iff_le_map, ← map_comp, map_comap_eq_of_surjective hg]

theorem Measurable.mono {ma ma' : SigmaAlgebra α} {mb mb' : SigmaAlgebra β} {f : α → β}
    (hf : @Measurable α β ma mb f) (ha : ma ≤ ma') (hb : mb' ≤ mb) : @Measurable α β ma' mb' f :=
  fun _t ht ↦ ha <| hf <| hb ht

lemma Measurable.iSup' {mα : ι → SigmaAlgebra α} {_ : SigmaAlgebra β} {f : α → β} (i₀ : ι)
    (h : Measurable[mα i₀] f) :
    Measurable[⨆ i, mα i] f :=
  h.mono (le_iSup mα i₀) le_rfl

lemma Measurable.sup_of_left {mα mα' : SigmaAlgebra α} {_ : SigmaAlgebra β} {f : α → β}
    (h : Measurable[mα] f) :
    Measurable[mα ⊔ mα'] f :=
  h.mono le_sup_left le_rfl

lemma Measurable.sup_of_right {mα mα' : SigmaAlgebra α} {_ : SigmaAlgebra β} {f : α → β}
    (h : Measurable[mα'] f) :
    Measurable[mα ⊔ mα'] f :=
  h.mono le_sup_right le_rfl

theorem measurable_id'' {m mα : SigmaAlgebra α} (hm : m ≤ mα) : @Measurable α α mα m id :=
  measurable_id.mono le_rfl hm

theorem measurable_from_top [SigmaAlgebra β] {f : α → β} : Measurable[⊤] f := fun _ _ => trivial

theorem measurable_generateFrom [SigmaAlgebra α] {s : Set (Set β)} {f : α → β}
    (h : ∀ t ∈ s, MeasurableSet (f ⁻¹' t)) : @Measurable _ _ _ (generateFrom s) f :=
  Measurable.of_le_map <| generateFrom_le fun t ht ↦ by
    change MeasurableSet (f ⁻¹' t)
    exact h t ht

theorem mem_generateFrom_of_mem_supClosure {s : Set (Set α)} {t : Set α}
    (ht : t ∈ supClosure s) : t ∈ generateFrom s := by
  rcases ht with ⟨P, hP, PC, rfl⟩
  rw [Finset.sup'_eq_sup, Finset.sup_id_set_eq_sUnion]
  exact MeasurableSet.sUnion (Finset.countable_toSet P)
    (fun s hs ↦ mem_generateFrom (PC hs))

variable {f g : α → β}

section TypeclassSigmaAlgebra

variable [SigmaAlgebra α] [SigmaAlgebra β]

@[nontriviality]
theorem Subsingleton.measurable [Subsingleton α] : Measurable f := fun _ _ =>
  @Subsingleton.measurableSet α _ _ _

@[nontriviality, fun_prop]
theorem measurable_of_subsingleton_codomain [Subsingleton β] (f : α → β) : Measurable f :=
  fun s _ => Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s

@[to_additive (attr := fun_prop)]
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
  convert! @measurable_const α β _ _ (f default) using 2
  apply hf

@[fun_prop]
theorem measurable_natCast [NatCast α] (n : ℕ) : Measurable (n : β → α) :=
  @measurable_const α _ _ _ n

@[fun_prop]
theorem measurable_intCast [IntCast α] (n : ℤ) : Measurable (n : β → α) :=
  @measurable_const α _ _ _ n

theorem measurable_of_countable [Countable α] [MeasurableSingletonClass α] (f : α → β) :
    Measurable f := fun s _ =>
  (f ⁻¹' s).to_countable.measurableSet

theorem measurable_of_finite [Finite α] [MeasurableSingletonClass α] (f : α → β) : Measurable f :=
  measurable_of_countable f

end TypeclassSigmaAlgebra

variable {m : SigmaAlgebra α}

@[fun_prop]
theorem Measurable.iterate {f : α → α} (hf : Measurable f) : ∀ n, Measurable f^[n]
  | 0 => measurable_id
  | n + 1 => (Measurable.iterate hf n).comp hf

variable {mβ : SigmaAlgebra β}

@[measurability]
theorem measurableSet_preimage {t : Set β} (hf : Measurable f) (ht : MeasurableSet t) :
    MeasurableSet (f ⁻¹' t) :=
  hf ht

protected theorem MeasurableSet.preimage {t : Set β} (ht : MeasurableSet t) (hf : Measurable f) :
    MeasurableSet (f ⁻¹' t) :=
  hf ht

@[fun_prop]
protected theorem Measurable.piecewise {_ : DecidablePred (· ∈ s)} (hs : MeasurableSet s)
    (hf : Measurable f) (hg : Measurable g) : Measurable (piecewise s f g) :=
  fun t ht ↦ by
    change MeasurableSet (piecewise s f g ⁻¹' t)
    simpa [piecewise_preimage] using hs.ite (hf ht) (hg ht)

/-- This is slightly different from `Measurable.piecewise`. It can be used to show
`Measurable (ite (x=0) 0 1)` by
`exact Measurable.ite (measurableSet_singleton 0) measurable_const measurable_const`,
but replacing `Measurable.ite` by `Measurable.piecewise` in that example proof does not work. -/
theorem Measurable.ite {p : α → Prop} {_ : DecidablePred p} (hp : MeasurableSet { a : α | p a })
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => ite (p x) (f x) (g x) :=
  Measurable.piecewise hp hf hg

@[fun_prop]
theorem Measurable.indicator [Zero β] (hf : Measurable f) (hs : MeasurableSet s) :
    Measurable (s.indicator f) :=
  hf.piecewise hs measurable_const

/-- The measurability of a set `A` is equivalent to the measurability of the indicator function
which takes a constant value `b ≠ 0` on a set `A` and `0` elsewhere. -/
lemma measurable_indicator_const_iff [Zero β] [MeasurableSingletonClass β] (b : β) [NeZero b] :
    Measurable (s.indicator (fun (_ : α) ↦ b)) ↔ MeasurableSet s := by
  constructor <;> intro h
  · convert! h (MeasurableSet.singleton (0 : β)).compl
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
  change MeasurableSet (g ⁻¹' t)
  have : g ⁻¹' t = g ⁻¹' t ∩ { x | f x = g x }ᶜ ∪ g ⁻¹' t ∩ { x | f x = g x } := by
    simp [← inter_union_distrib_left]
  rw [this]
  refine (h.mono inter_subset_right).measurableSet.union ?_
  have : g ⁻¹' t ∩ { x : α | f x = g x } = f ⁻¹' t ∩ { x : α | f x = g x } := by
    ext x
    simp +contextual
  rw [this]
  have hft : MeasurableSet (f ⁻¹' t) := by
    change f ⁻¹' t ∈ m
    exact hf ht
  exact hft.inter h.measurableSet.of_compl

end MeasurableFunctions

/-- We say that a collection of sets is countably spanning if a countable subset spans the
whole type. This is a useful condition in various parts of measure theory. For example, it is
a needed condition to show that the product of two collections generate the product sigma algebra,
see `generateFrom_prod_eq`. -/
def IsCountablySpanning (C : Set (Set α)) : Prop :=
  ∃ s : ℕ → Set α, (∀ n, s n ∈ C) ∧ ⋃ n, s n = univ

theorem isCountablySpanning_measurableSet [SigmaAlgebra α] :
    IsCountablySpanning { s : Set α | MeasurableSet s } :=
  ⟨fun _ => univ, fun _ => MeasurableSet.univ, iUnion_const _⟩

/-- Rectangles of countably spanning sets are countably spanning. -/
lemma IsCountablySpanning.prod {C : Set (Set α)} {D : Set (Set β)} (hC : IsCountablySpanning C)
    (hD : IsCountablySpanning D) : IsCountablySpanning (image2 (· ×ˢ ·) C D) := by
  rcases hC, hD with ⟨⟨s, h1s, h2s⟩, t, h1t, h2t⟩
  refine ⟨fun n => s n.unpair.1 ×ˢ t n.unpair.2, fun n => mem_image2_of_mem (h1s _) (h1t _), ?_⟩
  rw [iUnion_unpair_prod, h2s, h2t, univ_prod_univ]
