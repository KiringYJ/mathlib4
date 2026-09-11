/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.SigmaAlgebra.Defs
/-!
# σ-algebra of sets invariant under a self-map

In this file we define `SigmaAlgebra.invariants (f : α → α)`
to be the σ-algebra of sets `s : Set α` such that
- `s` is measurable w.r.t. the canonical σ-algebra on `α`;
- and `f ⁻¹' s = s`.
-/

@[expose] public section

open Set Function
open scoped MeasureTheory

namespace SigmaAlgebra

variable {α : Type*}

/-- Given a self-map `f : α → α`,
`invariants f` is the σ-algebra of measurable sets that are invariant under `f`.

A set `s` is `(invariants f)`-measurable
iff it is measurable w.r.t. the canonical σ-algebra on `α` and `f ⁻¹' s = s`. -/
@[instance_reducible]
def invariants [m : SigmaAlgebra α] (f : α → α) : SigmaAlgebra α :=
  { carrier := {s | s ∈ m ∧ f ⁻¹' s = s}
    isSigmaAlgebra :=
      { empty_mem := ⟨m.empty_mem, by simp⟩
        compl_mem := fun _ hs ↦ ⟨m.compl_mem hs.1, by simp [hs.2]⟩
        iUnion_mem_nat := fun s hs ↦
          ⟨m.iUnion_mem fun n ↦ (hs n).1, by simp [fun n ↦ (hs n).2]⟩ } }

variable [SigmaAlgebra α]

/-- A set `s` is `(invariants f)`-measurable
iff it is measurable w.r.t. the canonical σ-algebra on `α` and `f ⁻¹' s = s`. -/
theorem measurableSet_invariants {f : α → α} {s : Set α} :
    MeasurableSet[invariants f] s ↔ MeasurableSet s ∧ f ⁻¹' s = s := by
  change (s ∈ (inferInstance : SigmaAlgebra α) ∧ f ⁻¹' s = s) ↔
    s ∈ (inferInstance : SigmaAlgebra α) ∧ f ⁻¹' s = s
  rfl

@[simp]
theorem invariants_id : invariants (id : α → α) = ‹SigmaAlgebra α› :=
  ext fun _ ↦ ⟨And.left, fun h ↦ ⟨h, rfl⟩⟩

theorem invariants_le (f : α → α) : invariants f ≤ ‹SigmaAlgebra α› := fun _ ↦ And.left

theorem inf_le_invariants_comp (f g : α → α) :
    invariants f ⊓ invariants g ≤ invariants (f ∘ g) := fun s hs ↦
  ⟨hs.1.1, by rw [preimage_comp, hs.1.2, hs.2.2]⟩

theorem le_invariants_iterate (f : α → α) (n : ℕ) :
    invariants f ≤ invariants (f^[n]) := by
  induction n with
  | zero => simp [invariants_le]
  | succ n ihn => exact le_trans (le_inf ihn le_rfl) (inf_le_invariants_comp _ _)

variable {β : Type*} [SigmaAlgebra β]

theorem measurable_invariants_dom {f : α → α} {g : α → β} :
    Measurable[invariants f] g ↔ Measurable g ∧ ∀ s, MeasurableSet s → (g ∘ f) ⁻¹' s = g ⁻¹' s := by
  constructor
  · intro h
    constructor
    · intro s hs
      have hpre := h hs
      exact hpre.1
    · intro s hs
      have hpre := h hs
      change g ⁻¹' s ∈ (inferInstance : SigmaAlgebra α) ∧
        f ⁻¹' (g ⁻¹' s) = g ⁻¹' s at hpre
      simpa only [preimage_comp] using hpre.2
  · rintro ⟨hg, hinv⟩ s hs
    change g ⁻¹' s ∈ (inferInstance : SigmaAlgebra α) ∧
      f ⁻¹' (g ⁻¹' s) = g ⁻¹' s
    exact ⟨hg hs, by simpa only [preimage_comp] using hinv s hs⟩

theorem measurable_invariants_of_semiconj {fa : α → α} {fb : β → β} {g : α → β} (hg : Measurable g)
    (hfg : Semiconj g fa fb) : @Measurable _ _ (invariants fa) (invariants fb) g := fun s hs ↦
  ⟨hg hs.1, by rw [← preimage_comp, hfg.comp_eq, preimage_comp, hs.2]⟩

theorem comp_eq_of_measurable_invariants {f : α → α} {g : α → β} [MeasurableSingletonClass β]
    (h : Measurable[invariants f] g) : g ∘ f = g := by
  funext x
  suffices x ∈ f ⁻¹' g ⁻¹' {g x} by simpa
  rw [(h <| measurableSet_singleton (g x)).2, Set.mem_preimage, Set.mem_singleton_iff]

end SigmaAlgebra
