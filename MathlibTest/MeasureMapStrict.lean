import Mathlib.MeasureTheory.Measure.Map

/-!
# Strict measure pushforwards

These tests ensure that `Measure.map` exposes its a.e.-measurability obligation while retaining
automatic proof synthesis for routine measurable maps.
-/

open MeasureTheory

noncomputable section

variable {α β : Type*} [SigmaAlgebra α] [SigmaAlgebra β]

set_option linter.unusedVariables false in
example (μ : Measure α) (f : α → β) : True := by
  fail_if_success
    let _ν : Measure β := μ.map f
  trivial

set_option linter.unusedVariables false in
example (f : α → β) : True := by
  fail_if_success
    let _F : Measure α →ₗ[ENNReal] Measure β := Measure.mapₗ f
  trivial

set_option linter.unusedVariables false in
example (μ : Measure α) (f : α → β) : True := by
  fail_if_success
    let _ν : Measure β := (0 : ENNReal) • μ.map f
  trivial

example (μ : Measure α) (f : α → β) (hf : AEMeasurable f μ) : Measure β :=
  μ.map f

example (f : α → β) (hf : Measurable f) : Measure α →ₗ[ENNReal] Measure β :=
  Measure.mapₗ f

example (f : α → β) (hf₁ hf₂ : Measurable f) :
    Measure.mapₗ f hf₁ = Measure.mapₗ f hf₂ := rfl

example (μ : Measure α) (f : α → β) (hf₁ hf₂ : AEMeasurable f μ) :
    μ.map f hf₁ = μ.map f hf₂ := rfl

example (μ : Measure α) (f g : α → β) (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) (hfg : f =ᵐ[μ] g) : μ.map f hf = μ.map g hg := by
  simpa only using Measure.map_congr hfg hf

example (f : α → β) : (0 : Measure α).map f = 0 := by
  simp

example (μ : Measure α) (f : α → β) (hf : AEMeasurable f μ) {s : Set β}
    (hs : MeasurableSet s) : (μ.map f) s = μ (f ⁻¹' s) := by
  rw [Measure.map_apply hs]

variable {γ : Type*} [SigmaAlgebra γ]

example (μ : Measure α) (f : α → β) (g : β → γ) (hf : AEMeasurable f μ)
    (hg : AEMeasurable g (μ.map f)) : (μ.map f).map g = μ.map (g ∘ f) := by
  rw [Measure.map_map]
