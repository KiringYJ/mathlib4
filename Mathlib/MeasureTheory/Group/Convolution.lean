/-
Copyright (c) 2023 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
module

public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# The multiplicative and additive convolution of measures

In this file we define and prove properties about the convolutions of two measures.

## Main definitions

* `MeasureTheory.Measure.mconv`: The multiplicative convolution of two measures: the map of `*`
  under the product measure.
* `MeasureTheory.Measure.conv`: The additive convolution of two measures: the map of `+`
  under the product measure.
-/

@[expose] public section

namespace MeasureTheory

namespace Measure
open scoped ENNReal

variable {M : Type*} [Monoid M] [SigmaAlgebra M]

/-- Multiplicative convolution of measures. -/
@[to_additive /-- Additive convolution of measures. -/]
noncomputable def mconv [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) [SFinite ν] :
    Measure M :=
  Measure.map (fun x : M × M ↦ x.1 * x.2) (μ.productBySections ν) measurable_mul.aemeasurable

/-- Scoped notation for the multiplicative convolution of measures. -/
scoped[MeasureTheory] infixr:80 " ∗ₘ " => MeasureTheory.Measure.mconv

/-- Scoped notation for the additive convolution of measures. -/
scoped[MeasureTheory] infixr:80 " ∗ " => MeasureTheory.Measure.conv

@[to_additive]
theorem lintegral_mconv_eq_lintegral_prod [MeasurableMul₂ M] {μ ν : Measure M} [SFinite ν]
    {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(μ ∗ₘ ν) = ∫⁻ z, f (z.1 * z.2) ∂(μ.productBySections ν) := by
  rw [mconv, lintegral_map hf measurable_mul]

@[to_additive]
theorem lintegral_mconv [MeasurableMul₂ M] {μ ν : Measure M} [SFinite ν]
    {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(μ ∗ₘ ν) = ∫⁻ x, ∫⁻ y, f (x * y) ∂ν ∂μ := by
  rw [lintegral_mconv_eq_lintegral_prod hf, lintegral_productBySections _ (by fun_prop)]

@[to_additive]
lemma dirac_mconv [MeasurableMul₂ M] (x : M) (μ : Measure M) [SFinite μ] :
    (dirac x) ∗ₘ μ = μ.map (fun y ↦ x * y) := by
  unfold mconv
  calc
    map (fun x : M × M ↦ x.1 * x.2) ((dirac x).productBySections μ) measurable_mul.aemeasurable =
        map (fun x : M × M ↦ x.1 * x.2)
          (map (Prod.mk x) μ measurable_prodMk_left.aemeasurable) measurable_mul.aemeasurable :=
      congrArg (fun ρ ↦ map (fun p : M × M ↦ p.1 * p.2) ρ measurable_mul.aemeasurable)
        (dirac_productBySections x)
    _ = μ.map (fun y ↦ x * y) (by fun_prop) := by
      rw [map_map (by fun_prop) (by fun_prop)]
      simp [Function.comp_def]

@[to_additive]
lemma mconv_dirac [MeasurableMul₂ M] (μ : Measure M) [SFinite μ] (x : M) :
    μ ∗ₘ (dirac x) = μ.map (fun y ↦ y * x) := by
  unfold mconv
  calc
    map (fun x : M × M ↦ x.1 * x.2) (μ.productBySections (dirac x)) measurable_mul.aemeasurable =
        map (fun x : M × M ↦ x.1 * x.2)
          (map (fun y ↦ (y, x)) μ measurable_prodMk_right.aemeasurable)
          measurable_mul.aemeasurable :=
      congrArg (fun ρ ↦ map (fun p : M × M ↦ p.1 * p.2) ρ measurable_mul.aemeasurable)
        (productBySections_dirac x)
    _ = μ.map (fun y ↦ y * x) (by fun_prop) := by
      rw [map_map (by fun_prop) (by fun_prop)]
      simp [Function.comp_def]

@[to_additive (attr := simp)]
lemma dirac_mconv_dirac [MeasurableMul₂ M] (x y : M) :
    (dirac x) ∗ₘ (dirac y) = dirac (x * y) := by
  rw [mconv_dirac, map_dirac' (by fun_prop)]

/-- Convolution of the dirac measure at 1 with a measure μ returns μ. -/
@[to_additive (attr := simp)
/-- Convolution of the dirac measure at 0 with a measure μ returns μ. -/]
theorem dirac_one_mconv [MeasurableMul₂ M] (μ : Measure M) [SFinite μ] :
    (dirac 1) ∗ₘ μ = μ := by
  simp [dirac_mconv]

/-- Convolution of a measure μ with the dirac measure at 1 returns μ. -/
@[to_additive (attr := simp)
/-- Convolution of a measure μ with the dirac measure at 0 returns μ. -/]
theorem mconv_dirac_one [MeasurableMul₂ M]
    (μ : Measure M) [SFinite μ] : μ ∗ₘ (dirac 1) = μ := by
  simp [mconv_dirac]

/-- Convolution of the zero measure with a measure μ returns the zero measure. -/
@[to_additive (attr := simp) /-- Convolution of the zero measure with a measure μ returns
the zero measure. -/]
theorem zero_mconv [MeasurableMul₂ M] (μ : Measure M) [SFinite μ] :
    (0 : Measure M) ∗ₘ μ = (0 : Measure M) := by
  unfold mconv
  simp

/-- Convolution of a measure μ with the zero measure returns the zero measure. -/
@[to_additive (attr := simp) /-- Convolution of a measure μ with the zero measure returns the zero
measure. -/]
theorem mconv_zero [MeasurableMul₂ M] (μ : Measure M) :
    μ ∗ₘ (0 : Measure M) = (0 : Measure M) := by
  unfold mconv
  simp

-- `mconv_smul_right` needs an instance to get `SFinite (c • ν)` from `SFinite ν`,
-- hence it is placed in the `WithDensity` file, where the instance is defined.
@[to_additive conv_smul_left]
theorem mconv_smul_left [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) [SFinite ν] (s : ℝ≥0∞) :
    (s • μ) ∗ₘ ν = s • (μ ∗ₘ ν) := by
  unfold mconv
  calc
    map (fun x : M × M ↦ x.1 * x.2) ((s • μ).productBySections ν) measurable_mul.aemeasurable =
        map (fun x : M × M ↦ x.1 * x.2) (s • μ.productBySections ν) measurable_mul.aemeasurable :=
      congrArg (fun ρ ↦ map (fun p : M × M ↦ p.1 * p.2) ρ measurable_mul.aemeasurable)
        (Measure.productBySections_smul_left s)
    _ = s • map (fun x : M × M ↦ x.1 * x.2) (μ.productBySections ν) measurable_mul.aemeasurable :=
      Measure.map_smul s measurable_mul.aemeasurable

@[to_additive]
theorem mconv_add [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure M) [SFinite μ]
    [SFinite ν] [SFinite ρ] : μ ∗ₘ (ν + ρ) = μ ∗ₘ ν + μ ∗ₘ ρ := by
  unfold mconv
  calc
    map (fun x : M × M ↦ x.1 * x.2) (μ.productBySections (ν + ρ)) measurable_mul.aemeasurable =
        map (fun x : M × M ↦ x.1 * x.2) (μ.productBySections ν + μ.productBySections ρ)
          measurable_mul.aemeasurable :=
      congrArg (fun τ ↦ map (fun p : M × M ↦ p.1 * p.2) τ measurable_mul.aemeasurable)
        (productBySections_add ρ)
    _ = map (fun x : M × M ↦ x.1 * x.2) (μ.productBySections ν) measurable_mul.aemeasurable +
        map (fun x : M × M ↦ x.1 * x.2) (μ.productBySections ρ) measurable_mul.aemeasurable :=
      Measure.map_add _ _ measurable_mul

@[to_additive]
theorem add_mconv [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure M) [SFinite μ]
    [SFinite ν] [SFinite ρ] : (μ + ν) ∗ₘ ρ = μ ∗ₘ ρ + ν ∗ₘ ρ := by
  unfold mconv
  calc
    map (fun x : M × M ↦ x.1 * x.2) ((μ + ν).productBySections ρ) measurable_mul.aemeasurable =
        map (fun x : M × M ↦ x.1 * x.2) (μ.productBySections ρ + ν.productBySections ρ)
          measurable_mul.aemeasurable :=
      congrArg (fun τ ↦ map (fun p : M × M ↦ p.1 * p.2) τ measurable_mul.aemeasurable)
        (add_productBySections ν)
    _ = map (fun x : M × M ↦ x.1 * x.2) (μ.productBySections ρ) measurable_mul.aemeasurable +
        map (fun x : M × M ↦ x.1 * x.2) (ν.productBySections ρ) measurable_mul.aemeasurable :=
      Measure.map_add _ _ measurable_mul

/-- To get commutativity, we need the underlying multiplication to be commutative. -/
@[to_additive /-- To get commutativity, we need the underlying addition to be commutative. -/]
theorem mconv_comm {M : Type*} [CommMonoid M] [SigmaAlgebra M] [MeasurableMul₂ M] (μ : Measure M)
    (ν : Measure M) [SFinite μ] [SFinite ν] : μ ∗ₘ ν = ν ∗ₘ μ := by
  unfold mconv
  calc
    map (fun x : M × M ↦ x.1 * x.2) (μ.productBySections ν) measurable_mul.aemeasurable =
        map (fun x : M × M ↦ x.1 * x.2)
          (map Prod.swap (ν.productBySections μ) measurable_swap.aemeasurable)
          measurable_mul.aemeasurable :=
      congrArg (fun ρ ↦ map (fun p : M × M ↦ p.1 * p.2) ρ measurable_mul.aemeasurable)
        productBySections_swap.symm
    _ = map ((fun x : M × M ↦ x.1 * x.2) ∘ Prod.swap) (ν.productBySections μ) (by fun_prop) :=
      map_map (by fun_prop) (by fun_prop)
    _ = map (fun x : M × M ↦ x.1 * x.2) (ν.productBySections μ) measurable_mul.aemeasurable := by
      congr 1
      funext x
      simp [mul_comm]

/-- The convolution of s-finite measures is s-finite. -/
@[to_additive /-- The convolution of s-finite measures is s-finite. -/]
instance sfinite_mconv_of_sfinite [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M)
    [SFinite μ] [SFinite ν] : SFinite (μ ∗ₘ ν) :=
  inferInstanceAs <|
    SFinite ((μ.productBySections ν).map (fun (x : M × M) ↦ x.1 * x.2) measurable_mul.aemeasurable)

@[to_additive]
instance finite_of_finite_mconv [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : IsFiniteMeasure (μ ∗ₘ ν) := by
  have h : (μ ∗ₘ ν) Set.univ < ⊤ := by
    unfold mconv
    exact IsFiniteMeasure.measure_univ_lt_top
  exact { measure_univ_lt_top := h }

/-- Convolution is associative. -/
@[to_additive /-- Convolution is associative. -/]
theorem mconv_assoc [MeasurableMul₂ M] (μ ν ρ : Measure M)
    [SFinite ν] [SFinite ρ] :
    (μ ∗ₘ ν) ∗ₘ ρ = μ ∗ₘ (ν ∗ₘ ρ) := by
  refine ext_of_lintegral _ fun f hf ↦ ?_
  repeat rw [lintegral_mconv (by fun_prop)]
  refine lintegral_congr fun x ↦ ?_
  rw [lintegral_mconv (by fun_prop)]
  repeat refine lintegral_congr fun x ↦ ?_
  simp [mul_assoc]

@[to_additive]
instance probabilitymeasure_of_probabilitymeasures_mconv [MeasurableMul₂ M]
    (μ : Measure M) (ν : Measure M)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (μ ∗ₘ ν) := by
  rw [mconv]
  infer_instance

@[to_additive]
theorem mconv_absolutelyContinuous [MeasurableMul₂ M] {μ ν ρ : Measure M}
    [IsMulLeftInvariant ρ] [SFinite ν] (hν : ν ≪ ρ) : μ ∗ₘ ν ≪ ρ := by
  refine AbsolutelyContinuous.mk (fun s hs h ↦ ?_)
  rw [← lintegral_indicator_one hs, lintegral_mconv (by measurability)]
  conv in s.indicator 1 (_ * _) => change s.indicator 1 ((fun y ↦ x * y) y)
  simp only [← Set.indicator_comp_right, Pi.one_comp]
  conv in ∫⁻ _, _ ∂ν =>
    rw [lintegral_indicator_one (by apply MeasurableSet.preimage hs (by fun_prop))]
  have h0 (x : M) : ν (HMul.hMul x ⁻¹' s) = 0 := by
    apply hν
    rw [← map_apply hs, IsMulLeftInvariant.map_mul_left_eq_self, h]
  simp [h0]

@[to_additive]
lemma map_mconv_monoidHom {M M' : Type*} {mM : SigmaAlgebra M} [Monoid M] [MeasurableMul₂ M]
    {mM' : SigmaAlgebra M'} [Monoid M'] [MeasurableMul₂ M']
    {μ ν : Measure M} [SFinite μ] [SFinite ν]
    (L : M →* M') (hL : Measurable L) :
    (μ ∗ₘ ν).map L hL.aemeasurable =
      (μ.map L hL.aemeasurable) ∗ₘ (ν.map L hL.aemeasurable) := by
  unfold mconv
  have : (L ∘ fun p : M × M ↦ p.1 * p.2) = (fun p : M' × M' ↦ p.1 * p.2) ∘ (Prod.map L L) := by
    ext; simp
  calc
    map L (map (fun p : M × M ↦ p.1 * p.2) (μ.productBySections ν) measurable_mul.aemeasurable)
        hL.aemeasurable =
      map (L ∘ fun p : M × M ↦ p.1 * p.2) (μ.productBySections ν) (by fun_prop) :=
        map_map (by fun_prop) hL.aemeasurable
    _ = map ((fun p : M' × M' ↦ p.1 * p.2) ∘ Prod.map L L) (μ.productBySections ν)
        (by fun_prop) := by
      congr 1
    _ = map (fun p : M' × M' ↦ p.1 * p.2)
        (map (Prod.map L L) (μ.productBySections ν) (by fun_prop)) measurable_mul.aemeasurable :=
      (map_map (by fun_prop) measurable_mul.aemeasurable).symm
    _ = map (fun p : M' × M' ↦ p.1 * p.2)
        ((map L μ hL.aemeasurable).productBySections (map L ν hL.aemeasurable))
        measurable_mul.aemeasurable := by
      congr 1
      exact (map_productBySections_map μ ν hL hL).symm

lemma map_conv_continuousLinearMap {E F : Type*} [AddCommMonoid E] [AddCommMonoid F]
    [Module ℝ E] [Module ℝ F] [TopologicalSpace E] [TopologicalSpace F]
    {mE : SigmaAlgebra E} [MeasurableAdd₂ E] {mF : SigmaAlgebra F} [MeasurableAdd₂ F]
    [OpensSigmaAlgebra E] [BorelSpace F]
    {μ ν : Measure E} [SFinite μ] [SFinite ν]
    (L : E →L[ℝ] F) :
    (μ ∗ ν).map L L.continuous.measurable.aemeasurable =
      (μ.map L L.continuous.measurable.aemeasurable) ∗
        (ν.map L L.continuous.measurable.aemeasurable) := by
  simpa using map_conv_addMonoidHom (μ := μ) (ν := ν) (L : E →+ F)
    L.continuous.measurable

end Measure

end MeasureTheory
