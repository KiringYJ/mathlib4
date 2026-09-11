/-
Copyright (c) 2024 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
module

public import Mathlib.MeasureTheory.SigmaAlgebra.Defs
public import Mathlib.Order.Filter.CountableInter

/-!
# Measurability modulo a filter

In this file we consider the general notion of measurability modulo a σ-filter.
Two important instances of this construction are null-measurability with respect to a measure,
where the filter is the collection of co-null sets, and
Baire-measurability with respect to a topology,
where the filter is the collection of comeager (residual) sets.
(not to be confused with measurability with respect to the sigma algebra
of Baire sets, which is sometimes also called this.)
TODO: Implement the latter.

## Main definitions

* `eventuallySigmaAlgebra`: A `SigmaAlgebra` on a type `α` consisting of sets which are
  `Filter.EventuallyEq` to a measurable set with respect to a given `CountableInterFilter` on `α`
  and `SigmaAlgebra` on `α`.
* `EventuallyMeasurableSet`: A `Prop` for sets which are measurable with respect to some
  `eventuallySigmaAlgebra`.
* `EventuallyMeasurable`: A `Prop` for functions which are measurable with respect to some
  `eventuallySigmaAlgebra` on the domain.

-/

@[expose] public section

open Filter Set SigmaAlgebra

variable {α : Type*} (m : SigmaAlgebra α) {s t : Set α}

/-- The `SigmaAlgebra` of sets which are measurable with respect to a given σ-algebra `m`
on `α`, modulo a given σ-filter `l` on `α`. -/
@[instance_reducible]
def eventuallySigmaAlgebra (l : Filter α) [CountableInterFilter l] : SigmaAlgebra α where
  carrier := {s | ∃ t ∈ m, s =ᶠ[l] t}
  isSigmaAlgebra :=
    { empty_mem := ⟨∅, m.empty_mem, EventuallyEq.refl _ _⟩
      compl_mem := fun _ ⟨t, ht, hts⟩ ↦ ⟨tᶜ, m.compl_mem ht, hts.compl⟩
      iUnion_mem_nat := fun s hs ↦ by
        choose t ht hts using hs
        exact ⟨⋃ i, t i, m.iUnion_mem ht, .countable_iUnion hts⟩ }

/-- We say a set `s` is an `EventuallyMeasurableSet` with respect to a given
σ-algebra `m` and σ-filter `l` if it differs from a set in `m` by a set in
the dual ideal of `l`. -/
def EventuallyMeasurableSet (l : Filter α) [CountableInterFilter l] (s : Set α) : Prop :=
  @MeasurableSet _ (eventuallySigmaAlgebra m l) s

variable {l : Filter α} [CountableInterFilter l]
variable {m}

theorem MeasurableSet.eventuallyMeasurableSet (hs : MeasurableSet s) :
    EventuallyMeasurableSet m l s :=
  ⟨s, hs, EventuallyEq.refl _ _⟩

theorem le_eventuallySigmaAlgebra : m ≤ eventuallySigmaAlgebra m l :=
  fun s hs ↦ by
    change ∃ t ∈ m, s =ᶠ[l] t
    exact ⟨s, hs, EventuallyEq.refl _ _⟩

theorem eventuallyMeasurableSet_of_mem_filter (hs : s ∈ l) : EventuallyMeasurableSet m l s :=
  ⟨univ, MeasurableSet.univ, eventuallyEqSet_univ.mpr hs⟩

/-- A set which is `EventuallyEq` to an `EventuallyMeasurableSet`
is an `EventuallyMeasurableSet`. -/
theorem EventuallyMeasurableSet.congr
    (ht : EventuallyMeasurableSet m l t) (hst : s =ᶠ[l] t) : EventuallyMeasurableSet m l s := by
  rcases ht with ⟨t', ht', htt'⟩
  exact ⟨t', ht', hst.trans htt'⟩

section instances

instance eventuallyMeasurableSingleton [MeasurableSingletonClass α] :
    @MeasurableSingletonClass α (eventuallySigmaAlgebra m l) :=
  @MeasurableSingletonClass.mk _ (_) <| fun x => (MeasurableSet.singleton x).eventuallyMeasurableSet

end instances

section EventuallyMeasurable

open Function

variable (m l) {β γ : Type*} [SigmaAlgebra β] [SigmaAlgebra γ]

/-- We say a function is `EventuallyMeasurable` with respect to a given
σ-algebra `m` and σ-filter `l` if the preimage of any measurable set is equal to some
`m`-measurable set modulo `l`.
Warning: This is not always the same as being equal to some `m`-measurable function modulo `l`.
In general it is weaker. See `Measurable.eventuallyMeasurable_of_eventuallyEq`.
*TODO*: Add lemmas about when these are equivalent. -/
def EventuallyMeasurable (f : α → β) : Prop := @Measurable _ _ (eventuallySigmaAlgebra m l) _ f

variable {m l} {f g : α → β} {h : β → γ}

theorem Measurable.eventuallyMeasurable (hf : Measurable f) : EventuallyMeasurable m l f :=
  hf.le le_eventuallySigmaAlgebra

theorem Measurable.comp_eventuallyMeasurable (hh : Measurable h) (hf : EventuallyMeasurable m l f) :
    EventuallyMeasurable m l (h ∘ f) :=
  hh.comp hf

/-- A function which is `EventuallyEq` to some `EventuallyMeasurable` function
is `EventuallyMeasurable`. -/
theorem EventuallyMeasurable.congr
    (hf : EventuallyMeasurable m l f) (hgf : g =ᶠ[l] f) : EventuallyMeasurable m l g :=
  fun _ hs => EventuallyMeasurableSet.congr (hf hs)
    (hgf.preimage _)

/-- A function which is `EventuallyEq` to some `Measurable` function is `EventuallyMeasurable`. -/
theorem Measurable.eventuallyMeasurable_of_eventuallyEq
    (hf : Measurable f) (hgf : g =ᶠ[l] f) : EventuallyMeasurable m l g :=
  hf.eventuallyMeasurable.congr hgf

end EventuallyMeasurable
