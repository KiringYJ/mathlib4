import Mathlib.MeasureTheory.Measure.Prod

/-!
# Domains of the product-measure constructions

The ordinary product needs uniqueness of the rectangle formula. The iterated measure needs
scalar almost-everywhere measurability of sections, while the primitive product is defined for
arbitrary measures. These tests exercise the distinct domains and their default evidence.
-/

noncomputable section

section Qualified

variable {α β : Type*} [SigmaAlgebra α] [SigmaAlgebra β]

-- Default evidence must work without opening the namespace of the construction.
example (μ : MeasureTheory.Measure α) (ν : MeasureTheory.Measure β)
    [MeasureTheory.SigmaFinite μ] [MeasureTheory.SigmaFinite ν] :
    MeasureTheory.Measure (α × β) :=
  MeasureTheory.Measure.prod μ ν

example (μ : MeasureTheory.Measure α) (ν : MeasureTheory.Measure β)
    [MeasureTheory.SFinite ν] : MeasureTheory.Measure (α × β) :=
  MeasureTheory.Measure.productBySections μ ν

example (ν : MeasureTheory.Measure β) : MeasureTheory.Measure (α × β) :=
  MeasureTheory.Measure.prod (0 : MeasureTheory.Measure α) ν

example (ν : MeasureTheory.Measure β) : MeasureTheory.Measure (Unit × β) :=
  MeasureTheory.Measure.prod (MeasureTheory.Measure.dirac Unit.unit) ν

example (μ : MeasureTheory.Measure α) (ν : MeasureTheory.Measure β)
    [MeasureTheory.SigmaFinite μ] [MeasureTheory.SigmaFinite ν] :
    MeasureTheory.Measure.prod μ ν = MeasureTheory.Measure.productBySections μ ν :=
  MeasureTheory.Measure.prod_eq_productBySections μ ν

end Qualified

open MeasureTheory Set

open scoped ENNReal

variable {α β : Type*} [SigmaAlgebra α] [SigmaAlgebra β]

set_option linter.unusedVariables false in
example (μ : Measure α) (ν : Measure β) : True := by
  fail_if_success
    let _ρ : Measure (α × β) := μ.prod ν
  fail_if_success
    have _h : (0 : ℝ≥0∞) • μ.prod ν = 0 := zero_smul ℝ≥0∞ _
  trivial

example {γ δ : Type*} [SigmaAlgebra γ] [SigmaAlgebra δ]
    (μ : Measure α) (ν : Measure β) (h : HasUniqueProduct μ ν)
    (f : α → γ) (g : β → δ) (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) :
    AEMeasurable (fun p : α × β => (f p.1, g p.2)) (μ.prod ν h) := by
  fun_prop

set_option linter.unusedVariables false in
example (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] : True := by
  fail_if_success
    let _ρ : Measure (α × β) := μ.prod ν
  fail_if_success
    have _h : HasUniqueProduct μ ν := hasUniqueProduct_of_sigmaFinite μ ν
  trivial

example (μ : Measure α) (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν] :
    IsProductMeasure μ ν (μ.prod ν) :=
  Measure.prod_isProductMeasure μ ν

example (μ : Measure α) (ν : Measure β) (h : HasUniqueProduct μ ν) :
    IsProductMeasure μ ν (μ.prod ν) :=
  Measure.prod_isProductMeasure μ ν

example (μ : Measure α) (ν : Measure β) (h₁ h₂ : HasUniqueProduct μ ν) :
    μ.prod ν h₁ = μ.prod ν h₂ := rfl

example (μ : Measure α) (ν : Measure β) (h : HasUniqueProduct μ ν) :
    μ.prod ν h = μ.primitiveProd ν := rfl

example (μ : Measure α) (ν : Measure β) (h : HasUniqueProduct μ ν)
    (s : Set α) (t : Set β) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (μ.prod ν) (s ×ˢ t) = μ s * ν t :=
  Measure.prod_prod s t hs ht

-- The other measure is arbitrary: uniqueness is not restricted to two sigma-finite factors.
example (ν : Measure β) : HasUniqueProduct (0 : Measure α) ν :=
  hasUniqueProduct_zero_left ν

example (μ : Measure α) : HasUniqueProduct μ (0 : Measure β) :=
  hasUniqueProduct_zero_right μ

example (ν : Measure β) : (0 : Measure α).prod ν = 0 := Measure.zero_prod ν

example (μ : Measure α) : μ.prod (0 : Measure β) = 0 := Measure.prod_zero μ

example (ν : Measure β) :
    IsProductMeasure (Measure.dirac Unit.unit) ν ((Measure.dirac Unit.unit).prod ν) :=
  Measure.prod_isProductMeasure _ _

set_option linter.unusedVariables false in
example (μ : Measure α) (ν : Measure β) : True := by
  fail_if_success
    let _ρ : Measure (α × β) := μ.productBySections ν
  trivial

set_option linter.unusedVariables false in
example (μ : Measure α) (ν : Measure β) (h : HasMeasurableSections μ ν) : True := by
  fail_if_success
    let _ρ : Measure (α × β) := μ.prod ν
  trivial

example (μ : Measure α) (ν : Measure β) [SFinite ν] :
    IsProductMeasure μ ν (μ.productBySections ν) :=
  Measure.productBySections_isProductMeasure μ ν

example (μ : Measure α) (ν : Measure β) (h : HasMeasurableSections μ ν) :
    IsProductMeasure μ ν (μ.productBySections ν) :=
  Measure.productBySections_isProductMeasure μ ν

example (μ : Measure α) (ν : Measure β) (h₁ h₂ : HasMeasurableSections μ ν) :
    μ.productBySections ν h₁ = μ.productBySections ν h₂ := rfl

example (μ : Measure α) (ν : Measure β) (h : HasMeasurableSections μ ν)
    {s : Set (α × β)} (hs : MeasurableSet s) :
    (μ.productBySections ν) s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ :=
  Measure.productBySections_apply hs

example (μ : Measure α) (ν : Measure β)
    (hprod : AEMeasurable
      (fun x : α => Measure.map (Prod.mk x) ν measurable_prodMk_left.aemeasurable) μ) :
    HasMeasurableSections μ ν :=
  HasMeasurableSections.of_aemeasurable hprod

example (μ : Measure α) (ν : Measure β)
    (hprod : AEMeasurable
      (fun x : α => Measure.map (Prod.mk x) ν measurable_prodMk_left.aemeasurable) μ) :
    μ.productBySections ν (HasMeasurableSections.of_aemeasurable hprod) =
      μ.bind (fun x : α => Measure.map (Prod.mk x) ν measurable_prodMk_left.aemeasurable) hprod :=
  Measure.productBySections_eq_bind hprod

example (ν : Measure β) : (0 : Measure α).productBySections ν = 0 :=
  Measure.productBySections_zero_left ν

example (μ : Measure α) : μ.productBySections (0 : Measure β) = 0 :=
  Measure.productBySections_zero_right μ

example (μ : Measure α) (ν : Measure β) : Measure (α × β) := μ.primitiveProd ν

example (μ : Measure α) (ν : Measure β) : IsProductMeasure μ ν (μ.primitiveProd ν) :=
  Measure.primitiveProd_isProductMeasure μ ν
