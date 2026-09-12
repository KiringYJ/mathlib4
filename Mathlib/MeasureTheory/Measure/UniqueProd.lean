/-
Copyright (c) 2026 KiringYJ. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KiringYJ
-/
module

public import Mathlib.MeasureTheory.Measure.ProductBySections
public import Mathlib.MeasureTheory.Measure.PrimitiveProd

/-!
# The unique product of measures

The ordinary product `Measure.prod μ ν` requires `HasUniqueProduct μ ν`: exactly one measure
satisfies the rectangle formula. Sigma-finite factors supply this evidence automatically, as
does a zero factor or a subsingleton carrier. The definition uses the primitive product, and
uniqueness identifies it with every other product measure, including the iterated construction
whenever its section functions are almost everywhere measurable.

The global product `MeasureSpace` instance uses this unique product and requires both factor
volumes to be sigma-finite. `MeasureSpace.prod` permits an explicit local instance
on any uniqueness domain; `MeasureSpace.productBySections` explicitly selects the
section-integral construction.
-/

@[expose] public section

noncomputable section

open Set Function ENNReal

namespace MeasureTheory

variable {α β γ δ : Type*}
variable [SigmaAlgebra α] [SigmaAlgebra β] [SigmaAlgebra γ] [SigmaAlgebra δ]
variable {μ : Measure α} {ν : Measure β} {ρ : Measure (α × β)}

/-- Sigma-finite measures determine a unique product measure. -/
theorem hasUniqueProduct_of_sigmaFinite (μ : Measure α) (ν : Measure β)
    [SigmaFinite μ] [SigmaFinite ν] : HasUniqueProduct μ ν := by
  refine ⟨μ.productBySections ν, Measure.productBySections_isProductMeasure μ ν, ?_⟩
  intro ρ hρ
  exact (Measure.productBySections_eq fun s t hs ht => hρ hs ht).symm

/-- A subsingleton first factor determines a unique product, even for measures with infinite mass.
Every measurable set in the product is then a measurable rectangle. -/
theorem hasUniqueProduct_of_subsingleton_left (μ : Measure α) (ν : Measure β)
    [Subsingleton α] : HasUniqueProduct μ ν := by
  refine ⟨μ.primitiveProd ν, Measure.primitiveProd_isProductMeasure μ ν, fun ρ hρ => ?_⟩
  cases isEmpty_or_nonempty α with
  | inl h => exact Subsingleton.elim _ _
  | inr h =>
    obtain ⟨x⟩ := h
    ext s hs
    have heq : s = univ ×ˢ (Prod.mk x ⁻¹' s) := by
      ext ⟨a, b⟩
      simp [Subsingleton.elim a x]
    rw [heq, hρ MeasurableSet.univ (measurable_prodMk_left hs),
      Measure.primitiveProd_prod μ ν MeasurableSet.univ (measurable_prodMk_left hs)]

/-- A subsingleton second factor determines a unique product. -/
theorem hasUniqueProduct_of_subsingleton_right (μ : Measure α) (ν : Measure β)
    [Subsingleton β] : HasUniqueProduct μ ν :=
  (hasUniqueProduct_of_subsingleton_left ν μ).swap

namespace Measure

/-- The product of two measures on its exact uniqueness domain. Its rectangle formula determines
the result independently of the primitive construction used in this definition. -/
protected def prod (μ : Measure α) (ν : Measure β)
    (_h : HasUniqueProduct μ ν := by
      first
      | assumption
      | exact MeasureTheory.hasUniqueProduct_zero_left _
      | exact MeasureTheory.hasUniqueProduct_zero_right _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_left _ _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_right _ _
      | exact MeasureTheory.hasUniqueProduct_of_sigmaFinite _ _) : Measure (α × β) :=
  μ.primitiveProd ν

/-- The unique product is the primitive rectangle-cover product. -/
theorem prod_eq_primitiveProd (μ : Measure α) (ν : Measure β)
    (h : HasUniqueProduct μ ν := by
      first
      | assumption
      | exact MeasureTheory.hasUniqueProduct_zero_left _
      | exact MeasureTheory.hasUniqueProduct_zero_right _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_left _ _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_right _ _
      | exact MeasureTheory.hasUniqueProduct_of_sigmaFinite _ _) :
    μ.prod ν h = μ.primitiveProd ν := rfl

/-- The unique product satisfies the product formula on measurable rectangles. -/
theorem prod_isProductMeasure (μ : Measure α) (ν : Measure β)
    (h : HasUniqueProduct μ ν := by
      first
      | assumption
      | exact MeasureTheory.hasUniqueProduct_zero_left _
      | exact MeasureTheory.hasUniqueProduct_zero_right _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_left _ _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_right _ _
      | exact MeasureTheory.hasUniqueProduct_of_sigmaFinite _ _) :
    IsProductMeasure μ ν (μ.prod ν h) :=
  primitiveProd_isProductMeasure μ ν

/-- The product formula for measurable rectangles on the exact uniqueness domain. -/
@[simp]
theorem prod_prod (s : Set α) (t : Set β) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : HasUniqueProduct μ ν := by
      first
      | assumption
      | exact MeasureTheory.hasUniqueProduct_zero_left _
      | exact MeasureTheory.hasUniqueProduct_zero_right _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_left _ _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_right _ _
      | exact MeasureTheory.hasUniqueProduct_of_sigmaFinite _ _) :
    (μ.prod ν h) (s ×ˢ t) = μ s * ν t :=
  prod_isProductMeasure μ ν h hs ht

/-- A measure satisfying the rectangle formula is the unique product. -/
theorem prod_eq (hρ : ∀ s t, MeasurableSet s → MeasurableSet t →
    ρ (s ×ˢ t) = μ s * ν t)
    (h : HasUniqueProduct μ ν := by
      first
      | assumption
      | exact MeasureTheory.hasUniqueProduct_zero_left _
      | exact MeasureTheory.hasUniqueProduct_zero_right _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_left _ _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_right _ _
      | exact MeasureTheory.hasUniqueProduct_of_sigmaFinite _ _) : μ.prod ν h = ρ :=
  h.eq (prod_isProductMeasure μ ν h) (fun _ _ hs ht => hρ _ _ hs ht)

/-- On the common domain, the unique product agrees with integration of vertical sections. -/
theorem prod_eq_productBySections (μ : Measure α) (ν : Measure β)
    (hsections : HasAEMeasurableSectionMeasures μ ν := by
      first
      | assumption
      | exact MeasureTheory.hasAEMeasurableSectionMeasures_zero_left _
      | exact MeasureTheory.hasAEMeasurableSectionMeasures_of_sfinite _ _)
    (h : HasUniqueProduct μ ν := by
      first
      | assumption
      | exact MeasureTheory.hasUniqueProduct_zero_left _
      | exact MeasureTheory.hasUniqueProduct_zero_right _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_left _ _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_right _ _
      | exact MeasureTheory.hasUniqueProduct_of_sigmaFinite _ _) :
    μ.prod ν h = μ.productBySections ν hsections :=
  h.eq (prod_isProductMeasure μ ν h) (productBySections_isProductMeasure μ ν hsections)

/-- The section-integral formula for the unique product, with its measurability obligation. -/
theorem prod_apply {s : Set (α × β)} (hs : MeasurableSet s)
    (hsections : HasAEMeasurableSectionMeasures μ ν := by
      first
      | assumption
      | exact MeasureTheory.hasAEMeasurableSectionMeasures_zero_left _
      | exact MeasureTheory.hasAEMeasurableSectionMeasures_of_sfinite _ _)
    (h : HasUniqueProduct μ ν := by
      first
      | assumption
      | exact MeasureTheory.hasUniqueProduct_zero_left _
      | exact MeasureTheory.hasUniqueProduct_zero_right _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_left _ _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_right _ _
      | exact MeasureTheory.hasUniqueProduct_of_sigmaFinite _ _) :
    (μ.prod ν h) s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ := by
  rw [prod_eq_productBySections μ ν hsections h, productBySections_apply hs hsections]

/-- For sigma-finite factors, the rectangle formula holds without measurability of the sides. -/
@[simp]
theorem prod_prod_of_sigmaFinite [SigmaFinite μ] [SigmaFinite ν]
    (s : Set α) (t : Set β) : (μ.prod ν) (s ×ˢ t) = μ s * ν t := by
  rw [prod_eq_productBySections μ ν, productBySections_prod]

@[simp]
theorem zero_prod (ν : Measure β) : (0 : Measure α).prod ν = 0 :=
  prod_eq (fun _ _ _ _ => by simp)

@[simp]
theorem prod_zero (μ : Measure α) : μ.prod (0 : Measure β) = 0 :=
  prod_eq (fun _ _ _ _ => by simp)

/-- A product with a Dirac measure fixes the second coordinate. -/
theorem prod_dirac (y : β)
    (h : HasUniqueProduct μ (dirac y) := by
      first
      | assumption
      | exact MeasureTheory.hasUniqueProduct_zero_left _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_left _ _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_right _ _
      | exact MeasureTheory.hasUniqueProduct_of_sigmaFinite _ _) :
    μ.prod (dirac y) h = μ.map (fun x => (x, y)) measurable_prodMk_right.aemeasurable := by
  classical
  refine prod_eq (h := h) fun s t hs ht => ?_
  simp_rw [map_apply (hs.prod ht) measurable_prodMk_right.aemeasurable,
    mk_preimage_prod_left_eq_if, measure_if, dirac_apply' _ ht,
    ← indicator_mul_right _ fun _ => μ s, Pi.one_apply, mul_one]

/-- A product with a Dirac measure fixes the first coordinate. -/
theorem dirac_prod (x : α)
    (h : HasUniqueProduct (dirac x) ν := by
      first
      | assumption
      | exact MeasureTheory.hasUniqueProduct_zero_right _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_left _ _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_right _ _
      | exact MeasureTheory.hasUniqueProduct_of_sigmaFinite _ _) :
    (dirac x).prod ν h = ν.map (Prod.mk x) measurable_prodMk_left.aemeasurable := by
  classical
  refine prod_eq (h := h) fun s t hs ht => ?_
  simp_rw [map_apply (hs.prod ht) measurable_prodMk_left.aemeasurable,
    mk_preimage_prod_right_eq_if, measure_if, dirac_apply' _ hs,
    ← indicator_mul_left _ _ fun _ => ν t, Pi.one_apply, one_mul]

theorem dirac_prod_dirac {x : α} {y : β} :
    (dirac x).prod (dirac y) = dirac (x, y) := by
  rw [prod_dirac, map_dirac' measurable_prodMk_right]

/-- Swapping the coordinates of the unique product gives the product in the opposite order. -/
theorem prod_swap
    (h : HasUniqueProduct μ ν := by
      first
      | assumption
      | exact MeasureTheory.hasUniqueProduct_zero_left _
      | exact MeasureTheory.hasUniqueProduct_zero_right _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_left _ _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_right _ _
      | exact MeasureTheory.hasUniqueProduct_of_sigmaFinite _ _) :
    (μ.prod ν h).map Prod.swap measurable_swap.aemeasurable = ν.prod μ h.swap :=
  h.swap.eq (prod_isProductMeasure μ ν h).swap (prod_isProductMeasure ν μ h.swap)

theorem measurePreserving_swap
    (h : HasUniqueProduct μ ν := by
      first
      | assumption
      | exact MeasureTheory.hasUniqueProduct_zero_left _
      | exact MeasureTheory.hasUniqueProduct_zero_right _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_left _ _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_right _ _
      | exact MeasureTheory.hasUniqueProduct_of_sigmaFinite _ _) :
    MeasurePreserving Prod.swap (μ.prod ν h) (ν.prod μ h.swap) :=
  ⟨measurable_swap, prod_swap h⟩

/-- The symmetric section-integral formula for the unique product. -/
theorem prod_apply_symm {s : Set (α × β)} (hs : MeasurableSet s)
    (hsections : HasAEMeasurableSectionMeasures ν μ := by
      first
      | assumption
      | exact MeasureTheory.hasAEMeasurableSectionMeasures_zero_left _
      | exact MeasureTheory.hasAEMeasurableSectionMeasures_of_sfinite _ _)
    (h : HasUniqueProduct μ ν := by
      first
      | assumption
      | exact MeasureTheory.hasUniqueProduct_zero_left _
      | exact MeasureTheory.hasUniqueProduct_zero_right _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_left _ _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_right _ _
      | exact MeasureTheory.hasUniqueProduct_of_sigmaFinite _ _) :
    (μ.prod ν h) s = ∫⁻ y, μ ((fun x => (x, y)) ⁻¹' s) ∂ν := by
  rw [← prod_swap h.swap, map_apply hs measurable_swap.aemeasurable,
    prod_apply (measurable_swap hs) hsections h.swap]
  rfl

@[simp]
theorem map_fst_prod
    (h : HasUniqueProduct μ ν := by
      first
      | assumption
      | exact MeasureTheory.hasUniqueProduct_zero_left _
      | exact MeasureTheory.hasUniqueProduct_zero_right _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_left _ _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_right _ _
      | exact MeasureTheory.hasUniqueProduct_of_sigmaFinite _ _) :
    (μ.prod ν h).map Prod.fst measurable_fst.aemeasurable = (ν univ) • μ := by
  ext s hs
  rw [map_apply hs measurable_fst.aemeasurable, ← prod_univ,
    prod_prod s univ hs MeasurableSet.univ h, smul_apply, smul_eq_mul, mul_comm]

@[simp]
theorem map_snd_prod
    (h : HasUniqueProduct μ ν := by
      first
      | assumption
      | exact MeasureTheory.hasUniqueProduct_zero_left _
      | exact MeasureTheory.hasUniqueProduct_zero_right _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_left _ _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_right _ _
      | exact MeasureTheory.hasUniqueProduct_of_sigmaFinite _ _) :
    (μ.prod ν h).map Prod.snd measurable_snd.aemeasurable = (μ univ) • ν := by
  ext t ht
  rw [map_apply ht measurable_snd.aemeasurable, ← univ_prod,
    prod_prod univ t MeasurableSet.univ ht h, smul_apply, smul_eq_mul]

/-- The first projection pulls null sets back to null sets for a unique product. -/
@[fun_prop]
theorem quasiMeasurePreserving_fst_prod
    (h : HasUniqueProduct μ ν := by
      first
      | assumption
      | exact MeasureTheory.hasUniqueProduct_zero_left _
      | exact MeasureTheory.hasUniqueProduct_zero_right _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_left _ _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_right _ _
      | exact MeasureTheory.hasUniqueProduct_of_sigmaFinite _ _) :
    QuasiMeasurePreserving Prod.fst (μ.prod ν h) μ := by
  refine ⟨measurable_fst, AbsolutelyContinuous.mk fun s _ hs => ?_⟩
  simp only [map_fst_prod h, smul_apply, smul_eq_mul, hs, mul_zero]

/-- The second projection pulls null sets back to null sets for a unique product. -/
@[fun_prop]
theorem quasiMeasurePreserving_snd_prod
    (h : HasUniqueProduct μ ν := by
      first
      | assumption
      | exact MeasureTheory.hasUniqueProduct_zero_left _
      | exact MeasureTheory.hasUniqueProduct_zero_right _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_left _ _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_right _ _
      | exact MeasureTheory.hasUniqueProduct_of_sigmaFinite _ _) :
    QuasiMeasurePreserving Prod.snd (μ.prod ν h) ν := by
  refine ⟨measurable_snd, AbsolutelyContinuous.mk fun s _ hs => ?_⟩
  simp only [map_snd_prod h, smul_apply, smul_eq_mul, hs, mul_zero]

instance prod.instSigmaFinite [SigmaFinite μ] [SigmaFinite ν] : SigmaFinite (μ.prod ν) := by
  rw [prod_eq_productBySections μ ν]
  infer_instance

instance prod.instIsFiniteMeasure [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsFiniteMeasure (μ.prod ν) := by
  rw [prod_eq_productBySections μ ν]
  infer_instance

instance prod.instIsProbabilityMeasure [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (μ.prod ν) := by
  rw [prod_eq_productBySections μ ν]
  infer_instance

/-- Coordinatewise pushforwards commute with the unique product when both product domains hold. -/
theorem map_prod_map {f : α → γ} {g : β → δ} (μ : Measure α) (ν : Measure β)
    (hf : Measurable f) (hg : Measurable g)
    (hsource : HasUniqueProduct μ ν := by
      first
      | assumption
      | exact MeasureTheory.hasUniqueProduct_zero_left _
      | exact MeasureTheory.hasUniqueProduct_zero_right _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_left _ _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_right _ _
      | exact MeasureTheory.hasUniqueProduct_of_sigmaFinite _ _)
    (htarget : HasUniqueProduct (μ.map f hf.aemeasurable) (ν.map g hg.aemeasurable) := by
      first
      | assumption
      | exact MeasureTheory.hasUniqueProduct_of_sigmaFinite _ _) :
    (μ.map f hf.aemeasurable).prod (ν.map g hg.aemeasurable) htarget =
      (μ.prod ν hsource).map (Prod.map f g) (hf.prodMap hg).aemeasurable :=
  htarget.eq (prod_isProductMeasure _ _ htarget)
    ((prod_isProductMeasure μ ν hsource).map hf hg)

/-! ### The canonical ambient product measure -/

/-- Equip a product with its uniquely determined product measure. This explicit constructor
also covers uniqueness domains beyond sigma-finiteness, such as a zero measure or a subsingleton
carrier. It is not a global instance. -/
@[instance_reducible]
def _root_.MeasureTheory.MeasureSpace.prod (α β) [MeasureSpace α] [MeasureSpace β]
    (h : HasUniqueProduct (volume : Measure α) (volume : Measure β) := by
      first
      | assumption
      | exact MeasureTheory.hasUniqueProduct_zero_left _
      | exact MeasureTheory.hasUniqueProduct_zero_right _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_left _ _
      | exact MeasureTheory.hasUniqueProduct_of_subsingleton_right _ _
      | exact MeasureTheory.hasUniqueProduct_of_sigmaFinite _ _) : MeasureSpace (α × β) where
  volume := volume.prod volume h

/-- The ambient product of sigma-finite measure spaces uses their unique product measure. -/
instance prod.measureSpace {α β} [MeasureSpace α] [MeasureSpace β]
    [SigmaFinite (volume : Measure α)] [SigmaFinite (volume : Measure β)] :
    MeasureSpace (α × β) :=
  MeasureSpace.prod α β (hasUniqueProduct_of_sigmaFinite _ _)

/-- The canonical ambient product measure is the unique product of the factor volumes. -/
theorem volume_eq_prod (α β) [MeasureSpace α] [MeasureSpace β]
    [SigmaFinite (volume : Measure α)] [SigmaFinite (volume : Measure β)] :
    (volume : Measure (α × β)) = (volume : Measure α).prod (volume : Measure β) := rfl

/-- For sigma-finite factors, the ambient product also admits the section-integral formula. -/
theorem volume_eq_productBySections (α β) [MeasureSpace α] [MeasureSpace β]
    [SigmaFinite (volume : Measure α)] [SigmaFinite (volume : Measure β)] :
    (volume : Measure (α × β)) = (volume : Measure α).productBySections (volume : Measure β) :=
  prod_eq_productBySections _ _

instance {X Y : Type*}
    [TopologicalSpace X] [MeasureSpace X] [IsOpenPosMeasure (volume : Measure X)]
    [TopologicalSpace Y] [MeasureSpace Y] [IsOpenPosMeasure (volume : Measure Y)]
    [SigmaFinite (volume : Measure X)] [SigmaFinite (volume : Measure Y)] :
    IsOpenPosMeasure (volume : Measure (X × Y)) := by
  rw [volume_eq_productBySections]
  exact productBySections.instIsOpenPosMeasure

instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {m : MeasureSpace X} [IsLocallyFiniteMeasure (volume : Measure X)]
    {m' : MeasureSpace Y} [IsLocallyFiniteMeasure (volume : Measure Y)]
    [SigmaFinite (volume : Measure X)] [SigmaFinite (volume : Measure Y)] :
    IsLocallyFiniteMeasure (volume : Measure (X × Y)) := by
  rw [volume_eq_productBySections]
  exact productBySections.instIsLocallyFiniteMeasure

instance {α β : Type*} [MeasureSpace α] [MeasureSpace β] [IsFiniteMeasure (volume : Measure α)]
    [IsFiniteMeasure (volume : Measure β)] : IsFiniteMeasure (volume : Measure (α × β)) := by
  rw [volume_eq_productBySections]
  exact productBySections.instIsFiniteMeasure _ _

instance {α β : Type*} [MeasureSpace α] [MeasureSpace β]
    [IsProbabilityMeasure (volume : Measure α)] [IsProbabilityMeasure (volume : Measure β)] :
    IsProbabilityMeasure (volume : Measure (α × β)) := by
  rw [volume_eq_productBySections]
  exact productBySections.instIsProbabilityMeasure _ _

instance {X Y : Type*}
    [TopologicalSpace X] [MeasureSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)]
    [TopologicalSpace Y] [MeasureSpace Y] [IsFiniteMeasureOnCompacts (volume : Measure Y)]
    [SigmaFinite (volume : Measure X)] [SigmaFinite (volume : Measure Y)] :
    IsFiniteMeasureOnCompacts (volume : Measure (X × Y)) := by
  rw [volume_eq_productBySections]
  exact productBySections.instIsFiniteMeasureOnCompacts _ _

instance IsUnifLocDoublingMeasure.volume_prod {X Y : Type*} [PseudoMetricSpace X] [MeasureSpace X]
    [PseudoMetricSpace Y] [MeasureSpace Y]
    [SigmaFinite (volume : Measure X)] [SigmaFinite (volume : Measure Y)]
    [IsUnifLocDoublingMeasure (volume : Measure X)]
    [IsUnifLocDoublingMeasure (volume : Measure Y)] :
    IsUnifLocDoublingMeasure (volume : Measure (X × Y)) := by
  rw [volume_eq_productBySections]
  exact .prod _ _

instance {α β} [MeasureSpace α] [SigmaFinite (volume : Measure α)]
    [MeasureSpace β] [SigmaFinite (volume : Measure β)] :
    SigmaFinite (volume : Measure (α × β)) := by
  rw [volume_eq_productBySections]
  exact productBySections.instSigmaFinite

end Measure

/-- Tonelli's theorem for the unique product of sigma-finite measures. -/
theorem lintegral_prod [SigmaFinite μ] [SigmaFinite ν] (f : α × β → ℝ≥0∞)
    (hf : AEMeasurable f (μ.prod ν)) :
    ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  rw [Measure.prod_eq_productBySections μ ν] at hf ⊢
  exact lintegral_productBySections f hf

/-- Tonelli's theorem with the order of integration reversed. -/
theorem lintegral_prod_symm [SigmaFinite μ] [SigmaFinite ν] (f : α × β → ℝ≥0∞)
    (hf : AEMeasurable f (μ.prod ν)) :
    ∫⁻ z, f z ∂μ.prod ν = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν := by
  rw [Measure.prod_eq_productBySections μ ν] at hf ⊢
  exact lintegral_productBySections_symm f hf

theorem volume_preserving_prodAssoc {α₁ β₁ γ₁ : Type*} [MeasureSpace α₁]
    [MeasureSpace β₁] [MeasureSpace γ₁] [SigmaFinite (volume : Measure α₁)]
    [SigmaFinite (volume : Measure β₁)]
    [SigmaFinite (volume : Measure γ₁)] :
    MeasurePreserving (MeasurableEquiv.prodAssoc : (α₁ × β₁) × γ₁ ≃ᵐ α₁ × β₁ × γ₁) := by
  simp only [Measure.volume_eq_productBySections]
  exact MeasureTheory.measurePreserving_prodAssoc volume volume volume

end MeasureTheory
