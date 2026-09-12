/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Product measures and construction by section integrals

A product measure satisfies the product formula on measurable rectangles. The predicate
`IsProductMeasure μ ν ρ` records that formula, and `HasUniqueProduct μ ν` records existence
and uniqueness of a measure satisfying it.

The ordered construction `Measure.productBySections μ ν` integrates the measures of vertical
sections against `μ`. Its domain `HasAEMeasurableSectionMeasures μ ν` requires almost-everywhere
measurability of each scalar section-measure function. This holds whenever `ν` is s-finite.
The result is a product measure, but this construction does not assert uniqueness.
The API name is descriptive: it refers to construction through iterated integration, not to an
established binary-measure-theory term "iterated product measure". On a measurable set `s`,
`(μ.productBySections ν) s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ`.
-/

@[expose] public section

noncomputable section

open ENNReal MeasureTheory Set Function Real ENNReal SigmaAlgebra MeasureTheory.Measure
open TopologicalSpace hiding generateFrom
open Filter hiding prod_eq map

variable {α β : Type*}
variable [SigmaAlgebra α] [SigmaAlgebra β]
variable {μ : Measure α} {ν : Measure β}

/-- If `ν` is a finite measure, and `s ⊆ α × β` is measurable, then `x ↦ ν { y | (x, y) ∈ s }` is
  a measurable function. `measurable_measure_prodMk_left` is strictly more general. -/
theorem measurable_measure_prodMk_left_finite [IsFiniteMeasure ν] {s : Set (α × β)}
    (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻¹' s) := by
  induction s, hs using induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty => simp
  | basic s hs =>
    obtain ⟨s, hs, t, -, rfl⟩ := hs
    classical simpa only [mk_preimage_prod_right_eq_if, measure_if]
      using measurable_const.indicator hs
  | compl s hs ihs =>
    simp_rw [preimage_compl, measure_compl (measurable_prodMk_left hs) (measure_ne_top ν _)]
    exact ihs.const_sub _
  | iUnion f hfd hfm ihf =>
    have (a : α) : ν (Prod.mk a ⁻¹' ⋃ i, f i) = ∑' i, ν (Prod.mk a ⁻¹' f i) := by
      rw [preimage_iUnion, measure_iUnion]
      exacts [hfd.mono fun _ _ ↦ .preimage _, fun i ↦ measurable_prodMk_left (hfm i)]
    simpa only [this] using Measurable.tsum ihf

/-- If `ν` is an s-finite measure, and `s ⊆ α × β` is measurable, then `x ↦ ν { y | (x, y) ∈ s }`
is a measurable function.

Not true without the s-finite assumption: on `ℝ × ℝ` with the product sigma-algebra, let `s` be the
diagonal and let `ν` be an uncountable sum of Dirac measures (all Dirac measures for points in a
set `t`). Then `ν (Prod.mk x ⁻¹' s) = ν {x} = if x ∈ t then 1 else 0`. If `t` is chosen
non-measurable, this will not be measurable. -/
theorem measurable_measure_prodMk_left [SFinite ν] {s : Set (α × β)} (hs : MeasurableSet s) :
    Measurable fun x => ν (Prod.mk x ⁻¹' s) := by
  rw [← sum_sfiniteSeq ν]
  simp_rw [Measure.sum_apply_of_countable]
  exact Measurable.tsum (fun i ↦ measurable_measure_prodMk_left_finite hs)

/-- If `μ` is an s-finite measure, and `s ⊆ α × β` is measurable, then `y ↦ μ { x | (x, y) ∈ s }` is
  a measurable function. -/
theorem measurable_measure_prodMk_right {μ : Measure α} [SFinite μ] {s : Set (α × β)}
    (hs : MeasurableSet s) : Measurable fun y => μ ((fun x => (x, y)) ⁻¹' s) :=
  measurable_measure_prodMk_left (measurableSet_swap_iff.mpr hs)

@[fun_prop]
theorem Measurable.map_prodMk_left [SFinite ν] :
    Measurable fun x : α => map (Prod.mk x) ν measurable_prodMk_left.aemeasurable := by
  apply measurable_of_measurable_coe; intro s hs
  simp_rw [map_apply hs measurable_prodMk_left.aemeasurable]
  exact measurable_measure_prodMk_left hs

@[fun_prop]
theorem Measurable.map_prodMk_right {μ : Measure α} [SFinite μ] :
    Measurable fun y : β => map (fun x : α => (x, y)) μ measurable_prodMk_right.aemeasurable := by
  apply measurable_of_measurable_coe; intro s hs
  simp_rw [map_apply hs measurable_prodMk_right.aemeasurable]
  exact measurable_measure_prodMk_right hs

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  Tonelli's theorem is measurable. -/
theorem Measurable.lintegral_prod_right' [SFinite ν] :
    ∀ {f : α × β → ℝ≥0∞}, Measurable f → Measurable fun x => ∫⁻ y, f (x, y) ∂ν := by
  have m := @measurable_prodMk_left
  refine Measurable.ennreal_induction (motive := fun f ↦ Measurable fun (x : α) ↦ ∫⁻ y, f (x, y) ∂ν)
    ?_ ?_ ?_
  · intro c s hs
    simp only [← indicator_comp_right]
    suffices Measurable fun x => c * ν (Prod.mk x ⁻¹' s) by simpa [lintegral_indicator (m hs)]
    exact (measurable_measure_prodMk_left hs).const_mul _
  · rintro f g - hf - h2f h2g
    simp only [Pi.add_apply]
    conv => enter [1, x]; erw [lintegral_add_left (hf.comp m)]
    exact h2f.add h2g
  · intro f hf h2f h3f
    have : ∀ x, Monotone fun n y => f n (x, y) := fun x i j hij y => h2f hij (x, y)
    conv => enter [1, x]; erw [lintegral_iSup (fun n => (hf n).comp m) (this x)]
    exact .iSup h3f

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  Tonelli's theorem is measurable.
  This version has the argument `f` in curried form. -/
@[fun_prop]
theorem Measurable.lintegral_prod_right [SFinite ν] {f : α → β → ℝ≥0∞}
    (hf : Measurable (uncurry f)) : Measurable fun x => ∫⁻ y, f x y ∂ν :=
  hf.lintegral_prod_right'

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Tonelli's theorem is measurable. -/
theorem Measurable.lintegral_prod_left' [SFinite μ] {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun y => ∫⁻ x, f (x, y) ∂μ :=
  (measurable_swap_iff.mpr hf).lintegral_prod_right'

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Tonelli's theorem is measurable.
  This version has the argument `f` in curried form. -/
theorem Measurable.lintegral_prod_left [SFinite μ] {f : α → β → ℝ≥0∞}
    (hf : Measurable (uncurry f)) : Measurable fun y => ∫⁻ x, f x y ∂μ :=
  hf.lintegral_prod_left'

namespace MeasureTheory

/-- A measure on the product satisfies the product formula on measurable rectangles. -/
def IsProductMeasure (μ : Measure α) (ν : Measure β) (ρ : Measure (α × β)) : Prop :=
  ∀ ⦃s : Set α⦄ ⦃t : Set β⦄, MeasurableSet s → MeasurableSet t →
    ρ (s ×ˢ t) = μ s * ν t

/-- There is exactly one measure satisfying the product formula on measurable rectangles. -/
def HasUniqueProduct (μ : Measure α) (ν : Measure β) : Prop :=
  ∃! ρ, IsProductMeasure μ ν ρ

/-- Any two product measures agree when the factors determine a unique product. -/
theorem HasUniqueProduct.eq {ρ κ : Measure (α × β)} (h : HasUniqueProduct μ ν)
    (hρ : IsProductMeasure μ ν ρ) (hκ : IsProductMeasure μ ν κ) : ρ = κ :=
  ExistsUnique.unique h hρ hκ

/-- For every measurable subset of the product, its vertical section measures form a scalar
function that is almost everywhere measurable with respect to the first measure. -/
def HasAEMeasurableSectionMeasures (μ : Measure α) (ν : Measure β) : Prop :=
  ∀ ⦃s : Set (α × β)⦄, MeasurableSet s →
    AEMeasurable (fun x => ν (Prod.mk x ⁻¹' s)) μ

/-- Swapping the coordinates of a product measure reverses its factors. -/
theorem IsProductMeasure.swap {ρ : Measure (α × β)} (hρ : IsProductMeasure μ ν ρ) :
    IsProductMeasure ν μ (ρ.map Prod.swap measurable_swap.aemeasurable) := by
  intro s t hs ht
  rw [Measure.map_apply (hs.prod ht) measurable_swap.aemeasurable,
    preimage_swap_prod, hρ ht hs, mul_comm]

/-- Mapping a product measure coordinatewise preserves the rectangle formula. -/
theorem IsProductMeasure.map {γ δ : Type*} [SigmaAlgebra γ] [SigmaAlgebra δ]
    {ρ : Measure (α × β)} {f : α → γ} {g : β → δ}
    (hρ : IsProductMeasure μ ν ρ) (hf : Measurable f) (hg : Measurable g) :
    IsProductMeasure (μ.map f hf.aemeasurable) (ν.map g hg.aemeasurable)
      (ρ.map (Prod.map f g) (hf.prodMap hg).aemeasurable) := by
  intro s t hs ht
  rw [Measure.map_apply (hs.prod ht) (hf.prodMap hg).aemeasurable,
    Measure.map_apply hs hf.aemeasurable, Measure.map_apply ht hg.aemeasurable]
  exact hρ (hf hs) (hg ht)

/-- Uniqueness of the product is unchanged by exchanging its factors. -/
theorem HasUniqueProduct.swap (h : HasUniqueProduct μ ν) : HasUniqueProduct ν μ := by
  obtain ⟨ρ, hρ, huniq⟩ := h
  refine ⟨ρ.map Prod.swap measurable_swap.aemeasurable, hρ.swap, ?_⟩
  intro κ hκ
  have heq := huniq (κ.map Prod.swap measurable_swap.aemeasurable) hκ.swap
  apply (MeasurableEquiv.prodComm (α := β) (β := α)).map_measurableEquiv_injective
  change κ.map Prod.swap measurable_swap.aemeasurable =
    (ρ.map (MeasurableEquiv.prodComm (α := α) (β := β))).map
      (MeasurableEquiv.prodComm (α := α) (β := β)).symm
  rw [MeasurableEquiv.map_symm_map]
  exact heq

theorem hasUniqueProduct_swap_iff : HasUniqueProduct ν μ ↔ HasUniqueProduct μ ν :=
  ⟨HasUniqueProduct.swap, HasUniqueProduct.swap⟩

/-- Almost-everywhere measurability of the measure-valued section family implies scalar
almost-everywhere measurability of every measurable section evaluation. -/
theorem HasAEMeasurableSectionMeasures.of_aemeasurable
    (h : AEMeasurable
      (fun x : α => Measure.map (Prod.mk x) ν measurable_prodMk_left.aemeasurable) μ) :
    HasAEMeasurableSectionMeasures μ ν := by
  intro s hs
  simpa only [Function.comp_def, Measure.map_apply hs measurable_prodMk_left.aemeasurable]
    using (Measure.measurable_coe hs).comp_aemeasurable h

/-- An s-finite second measure has measurable section-measure functions. -/
theorem hasAEMeasurableSectionMeasures_of_sfinite (μ : Measure α) (ν : Measure β) [SFinite ν] :
    HasAEMeasurableSectionMeasures μ ν :=
  fun _ hs => (measurable_measure_prodMk_left hs).aemeasurable

/-- Every section-measure function is almost everywhere measurable for the zero first measure. -/
@[simp]
theorem hasAEMeasurableSectionMeasures_zero_left (ν : Measure β) :
    HasAEMeasurableSectionMeasures (0 : Measure α) ν :=
  fun _ _ => aemeasurable_zero_measure

/-- The zero measure satisfies the product formula when the first factor is zero. -/
theorem IsProductMeasure.zero_left (ν : Measure β) :
    IsProductMeasure (0 : Measure α) ν 0 := by
  intro s t hs ht
  simp

/-- The zero measure satisfies the product formula when the second factor is zero. -/
theorem IsProductMeasure.zero_right (μ : Measure α) :
    IsProductMeasure μ (0 : Measure β) 0 := by
  intro s t hs ht
  simp

/-- A zero first factor determines a unique product measure. -/
@[simp]
theorem hasUniqueProduct_zero_left (ν : Measure β) :
    HasUniqueProduct (0 : Measure α) ν := by
  refine ⟨0, IsProductMeasure.zero_left ν, fun ρ hρ => ?_⟩
  apply Measure.measure_univ_eq_zero.mp
  simpa using hρ MeasurableSet.univ MeasurableSet.univ

/-- A zero second factor determines a unique product measure. -/
@[simp]
theorem hasUniqueProduct_zero_right (μ : Measure α) :
    HasUniqueProduct μ (0 : Measure β) := by
  refine ⟨0, IsProductMeasure.zero_right μ, fun ρ hρ => ?_⟩
  apply Measure.measure_univ_eq_zero.mp
  simpa using hρ MeasurableSet.univ MeasurableSet.univ

namespace Measure

/-- The measure constructed by section integrals of vertical section measures.
Scalar almost-everywhere measurability of every measurable section is sufficient for this
construction; in particular, it is defined whenever the second measure is s-finite. -/
protected def productBySections (μ : Measure α) (ν : Measure β)
    (h : HasAEMeasurableSectionMeasures μ ν := by
      first
      | assumption
      | exact MeasureTheory.hasAEMeasurableSectionMeasures_zero_left _
      | exact MeasureTheory.hasAEMeasurableSectionMeasures_of_sfinite _ _) : Measure (α × β) :=
  Measure.ofMeasurable (fun s _ => ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ)
    (by simp)
    (by
      intro f hf hd
      have hUnion (x : α) :
          ν (Prod.mk x ⁻¹' ⋃ i, f i) = ∑' i, ν (Prod.mk x ⁻¹' f i) := by
        rw [preimage_iUnion, measure_iUnion]
        exacts [hd.mono fun _ _ ↦ .preimage _, fun i ↦ measurable_prodMk_left (hf i)]
      simp_rw [hUnion]
      exact lintegral_tsum fun i => h (hf i))

/-- On a measurable set, the measure constructed by section integrals is the integral of its
section measures. -/
theorem productBySections_apply {s : Set (α × β)} (hs : MeasurableSet s)
    (h : HasAEMeasurableSectionMeasures μ ν := by
      first
      | assumption
      | exact MeasureTheory.hasAEMeasurableSectionMeasures_zero_left _
      | exact MeasureTheory.hasAEMeasurableSectionMeasures_of_sfinite _ _) :
    (μ.productBySections ν h) s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ :=
  Measure.ofMeasurable_apply s hs

/-- A measure constructed by section integrals satisfies the product formula on measurable
rectangles. -/
theorem productBySections_isProductMeasure (μ : Measure α) (ν : Measure β)
    (h : HasAEMeasurableSectionMeasures μ ν := by
      first
      | assumption
      | exact MeasureTheory.hasAEMeasurableSectionMeasures_zero_left _
      | exact MeasureTheory.hasAEMeasurableSectionMeasures_of_sfinite _ _) :
    IsProductMeasure μ ν (μ.productBySections ν h) := by
  intro s t hs ht
  rw [productBySections_apply (hs.prod ht) h]
  classical
  simp_rw [mk_preimage_prod_right_eq_if, measure_if, lintegral_indicator hs,
    lintegral_const, restrict_apply_univ, mul_comm]

/-- Under measure-valued almost-everywhere measurability, the scalar section-integral
construction agrees with monadic bind. -/
theorem productBySections_eq_bind
    (hprod : AEMeasurable
      (fun x : α => map (Prod.mk x) ν measurable_prodMk_left.aemeasurable) μ) :
    μ.productBySections ν (HasAEMeasurableSectionMeasures.of_aemeasurable hprod) =
      μ.bind (fun x : α => map (Prod.mk x) ν measurable_prodMk_left.aemeasurable) hprod := by
  ext s hs
  rw [productBySections_apply hs (HasAEMeasurableSectionMeasures.of_aemeasurable hprod),
    bind_apply hs hprod]
  simp_rw [map_apply hs measurable_prodMk_left.aemeasurable]

@[simp]
theorem productBySections_zero_left (ν : Measure β) :
    (0 : Measure α).productBySections ν = 0 := by
  ext s hs
  simp [productBySections_apply (μ := 0) (ν := ν) hs]

@[simp]
theorem productBySections_zero_right (μ : Measure α) :
    μ.productBySections (0 : Measure β) = 0 := by
  ext s hs
  simp [productBySections_apply (μ := μ) (ν := 0) hs]

end Measure
end MeasureTheory
