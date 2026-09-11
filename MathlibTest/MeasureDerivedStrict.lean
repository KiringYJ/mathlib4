import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Strict APIs derived from measure pushforward

These tests ensure that constructions implemented through `Measure.map` do not reintroduce its
former invalid-domain fallbacks.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

variable {α β γ : Type*} [SigmaAlgebra α] [SigmaAlgebra β] [SigmaAlgebra γ]

set_option linter.unusedVariables false in
example (m : Measure α) (f : α → Measure β) : True := by
  fail_if_success
    let _n : Measure β := m.bind f
  trivial

example (m : Measure α) (f : α → Measure β) (hf : AEMeasurable f m) : Measure β :=
  m.bind f

example (m : Measure α) (f : α → Measure β) (hf₁ hf₂ : AEMeasurable f m) :
    m.bind f hf₁ = m.bind f hf₂ := rfl

example (m : Measure α) (f : α → Measure β) (g : β → Measure γ)
    (hf : AEMeasurable f m) (hg : Measurable g) :
    (m.bind f hf).bind g hg.aemeasurable =
      m.bind (fun a => (f a).bind g hg.aemeasurable)
        ((Measure.measurable_bind' hg).comp_aemeasurable hf) :=
  Measure.bind_bind hf hg

set_option linter.unusedVariables false in
example (μ : Measure α) (ν : Measure β) : True := by
  fail_if_success
    let _μν : Measure (α × β) := μ.prod ν
  trivial

example (μ : Measure α) (ν : Measure β) [SFinite ν] : Measure (α × β) :=
  μ.prod ν

example (ν : Measure β) : (0 : Measure α).prod ν = 0 := by
  simp

example (μ : Measure α) (ν : Measure β)
    (hprod : AEMeasurable
      (fun x : α => Measure.map (Prod.mk x) ν measurable_prodMk_left.aemeasurable) μ) :
    Measure (α × β) :=
  μ.prod ν hprod

example (μ : Measure α) (ν : Measure β)
    (hprod₁ hprod₂ : AEMeasurable
      (fun x : α => Measure.map (Prod.mk x) ν measurable_prodMk_left.aemeasurable) μ) :
    μ.prod ν hprod₁ = μ.prod ν hprod₂ := rfl

example (μ : Measure α) (ν : Measure β) {s : Set (α × β)} (hs : MeasurableSet s)
    (hprod : AEMeasurable
      (fun x : α => Measure.map (Prod.mk x) ν measurable_prodMk_left.aemeasurable) μ) :
    (μ.prod ν hprod) s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ :=
  Measure.prod_apply hs hprod

example (μ : Measure α) (ν : Measure β) (hν : SFinite ν) : Measure (α × β) :=
  μ.prod ν (by
    let _ : SFinite ν := hν
    fun_prop)

set_option linter.unusedVariables false in
example (κ : Kernel α β) (f : β → γ) : True := by
  fail_if_success
    let _κf : Kernel α γ := κ.map f
  trivial

example (κ : Kernel α β) (f : β → γ) (hf : Measurable f) : Kernel α γ :=
  κ.map f

example (κ : Kernel α β) (f : β → γ) (hf hf' : Measurable f) :
    κ.map f hf = κ.map f hf' := rfl

example (κ : Kernel α β) (f : β → γ) (hf : Measurable f) (a : α) :
    κ.map f hf a = (κ a).map f hf.aemeasurable := by
  rw [Kernel.map_apply]

example (κ : Kernel α β) (f : β → γ) (hf : Measurable f) (a : α)
    (s : Set γ) (hs : MeasurableSet s) : κ.map f hf a s = κ a (f ⁻¹' s) := by
  rw [Kernel.map_apply' _ _ hs]

example (κ : Kernel α β) (f g : β → γ) (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ a, f =ᵐ[κ a] g) : κ.map f hf = κ.map g hg :=
  Kernel.map_congr_ae κ hfg

set_option linter.unusedVariables false in
example (ν : FiniteMeasure α) (f : α → β) : True := by
  fail_if_success
    let _νf : FiniteMeasure β := ν.map f
  trivial

example (ν : FiniteMeasure α) (f : α → β) (hf : AEMeasurable f ν) :
    FiniteMeasure β :=
  ν.map f

example (ν : FiniteMeasure α) (f : α → β) (hf₁ hf₂ : AEMeasurable f ν) :
    ν.map f hf₁ = ν.map f hf₂ := rfl

set_option linter.unusedVariables false in
example (ν : ProbabilityMeasure α) (f : α → β) : True := by
  fail_if_success
    let _νf : ProbabilityMeasure β := ν.map f
  trivial

example (ν : ProbabilityMeasure α) (f : α → β) (hf : AEMeasurable f ν) :
    ProbabilityMeasure β :=
  ν.map f

example (ν : ProbabilityMeasure α) (f : α → β) (hf₁ hf₂ : AEMeasurable f ν) :
    ν.map f hf₁ = ν.map f hf₂ := rfl

variable {Ω : Type*} [SigmaAlgebra Ω] [StandardBorelSpace Ω] [Nonempty Ω]

set_option linter.unusedVariables false in
example (μ : Measure α) [IsFiniteMeasure μ] (X : α → β) (Y : α → Ω) : True := by
  fail_if_success
    let _κ : Kernel β Ω := condDistrib Y X μ
  trivial

example (μ : Measure α) [IsFiniteMeasure μ] (X : α → β) (Y : α → Ω)
    (hXY : AEMeasurable (fun a ↦ (X a, Y a)) μ) : Kernel β Ω :=
  condDistrib Y X μ

example (μ : Measure α) [IsFiniteMeasure μ] (X : α → β) (Y : α → Ω)
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) : Kernel β Ω :=
  condDistrib Y X μ

example (μ : Measure α) [IsFiniteMeasure μ] (X : α → β) (Y : α → Ω)
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    IsMarkovKernel (condDistrib Y X μ) := by
  infer_instance

example (μ : Measure α) [IsFiniteMeasure μ] (X : α → β) (Y : α → Ω)
    (hXY₁ hXY₂ : AEMeasurable (fun a ↦ (X a, Y a)) μ) :
    condDistrib Y X μ hXY₁ = condDistrib Y X μ hXY₂ := rfl
