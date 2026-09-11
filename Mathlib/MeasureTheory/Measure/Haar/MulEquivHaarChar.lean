/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Scaling Haar measure by a continuous isomorphism

If `G` is a locally compact topological group and `μ` is a regular Haar measure
on `G`, then an isomorphism `φ : G ≃ₜ* G` scales this measure by some positive
real constant which we call `mulEquivHaarChar φ`.

## Main definitions

* `mulEquivHaarChar φ`: the positive real such that `(mulEquivHaarChar φ) • map φ μ = μ`
  for `μ` a regular Haar measure.
* `addEquivAddHaarChar φ`: the additive version.

-/

@[expose] public section

open MeasureTheory.Measure

open scoped NNReal Pointwise ENNReal

namespace MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [SigmaAlgebra G]
    [BorelSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- If `φ : G ≃ₜ* G` then `mulEquivHaarChar φ` is the positive real factor by which
`φ` scales Haar measures on `G`. -/
@[to_additive /-- If `φ : A ≃ₜ+ A` then `addEquivAddHaarChar φ` is the positive
real factor by which `φ` scales Haar measures on `A`. -/]
noncomputable def mulEquivHaarChar (φ : G ≃ₜ* G) : ℝ≥0 :=
  haarScalarFactor haar (haar.map φ (map_continuous φ).measurable.aemeasurable)

@[to_additive]
lemma mulEquivHaarChar_pos (φ : G ≃ₜ* G) : 0 < mulEquivHaarChar φ :=
  haarScalarFactor_pos_of_isHaarMeasure _ _

@[to_additive]
lemma mulEquivHaarChar_eq (μ : Measure G) [IsHaarMeasure μ]
    [Regular μ] (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ =
      haarScalarFactor μ (μ.map φ (map_continuous φ).measurable.aemeasurable) := by
  have smul := isMulLeftInvariant_eq_smul_of_regular haar μ
  unfold mulEquivHaarChar
  conv =>
    enter [1, 1]
    rw [smul]
  conv =>
    enter [1, 2, 2]
    rw [smul]
  rw! [MeasureTheory.Measure.map_smul _ (by fun_prop)]
  exact haarScalarFactor_smul_smul _ _ (haarScalarFactor_pos_of_isHaarMeasure haar μ).ne'

@[to_additive addEquivAddHaarChar_smul_map]
lemma mulEquivHaarChar_smul_map (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ • μ.map φ (map_continuous φ).measurable.aemeasurable = μ := by
  rw [mulEquivHaarChar_eq μ φ]
  have : Regular (map φ μ (map_continuous φ).measurable.aemeasurable) :=
    Regular.map φ.toHomeomorph
  exact (isMulLeftInvariant_eq_smul_of_regular μ
    (map φ μ (map_continuous φ).measurable.aemeasurable)).symm

@[to_additive addEquivAddHaarChar_smul_eq_comap]
lemma mulEquivHaarChar_smul_eq_comap (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] (φ : G ≃ₜ* G) :
    (mulEquivHaarChar φ) • μ = μ.comap φ := by
  let e := φ.toHomeomorph.toMeasurableEquiv
  change (mulEquivHaarChar φ) • μ = μ.comap e
  rw [← e.map_symm]
  have : (map e.symm μ e.symm.measurable.aemeasurable).IsHaarMeasure :=
    φ.symm.isHaarMeasure_map μ
  have : (map e.symm μ e.symm.measurable.aemeasurable).Regular :=
    Regular.map φ.symm.toHomeomorph
  rw [← mulEquivHaarChar_smul_map (map e.symm μ e.symm.measurable.aemeasurable) φ,
    map_map e.symm.measurable.aemeasurable (map_continuous φ).measurable.aemeasurable]
  have hmap : map (φ ∘ e.symm) μ (by fun_prop) = μ := by
    calc
      map (φ ∘ e.symm) μ (by fun_prop) = map id μ measurable_id.aemeasurable := by
        apply Measure.map_congr (ae_of_all μ fun x ↦ by simp [e]) (by fun_prop)
      _ = μ := Measure.map_id
  rw [hmap]

@[to_additive addEquivAddHaarChar_smul_integral_map]
lemma mulEquivHaarChar_smul_integral_map (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] {f : G → ℝ} (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ •
      ∫ a, f a ∂(μ.map φ (map_continuous φ).measurable.aemeasurable) = ∫ a, f a ∂μ := by
  calc
    mulEquivHaarChar φ •
        ∫ a, f a ∂(μ.map φ (map_continuous φ).measurable.aemeasurable) =
      ∫ a, f a ∂(mulEquivHaarChar φ •
        μ.map φ (map_continuous φ).measurable.aemeasurable) := by
        rw [integral_smul_nnreal_measure]
    _ = ∫ a, f a ∂μ := by rw [mulEquivHaarChar_smul_map]

@[to_additive integral_comap_eq_addEquivAddHaarChar_smul]
lemma integral_comap_eq_mulEquivHaarChar_smul (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] {f : G → ℝ} (φ : G ≃ₜ* G) :
    ∫ a, f a ∂(μ.comap φ) = mulEquivHaarChar φ • ∫ a, f a ∂μ := by
  rw [← mulEquivHaarChar_smul_eq_comap μ φ, integral_smul_nnreal_measure]

@[to_additive addEquivAddHaarChar_smul_preimage]
lemma mulEquivHaarChar_smul_preimage
    (μ : Measure G) [IsHaarMeasure μ] [Regular μ] {X : Set G} (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ • μ (φ ⁻¹' X) = μ X := by
  nth_rw 2 [← mulEquivHaarChar_smul_map μ φ]
  simp only [Measure.smul_apply, nnreal_smul_coe_apply]
  exact congr_arg _ <| (MeasurableEquiv.map_apply φ.toMeasurableEquiv X).symm

@[to_additive (attr := simp)]
lemma mulEquivHaarChar_refl :
    mulEquivHaarChar (ContinuousMulEquiv.refl G) = 1 := by
  simp [mulEquivHaarChar, Function.id_def]

@[to_additive]
lemma mulEquivHaarChar_trans {φ ψ : G ≃ₜ* G} :
    mulEquivHaarChar (ψ.trans φ) = mulEquivHaarChar ψ * mulEquivHaarChar φ := by
  rw [mulEquivHaarChar_eq haar ψ, mulEquivHaarChar_eq haar (ψ.trans φ)]
  have hφ : Measurable φ := by fun_prop
  have hψ : Measurable ψ := by fun_prop
  simp_rw [ContinuousMulEquiv.coe_trans, ← map_map hψ.aemeasurable hφ.aemeasurable]
  have h_reg : (haar.map ψ hψ.aemeasurable).Regular := Regular.map ψ.toHomeomorph
  rw [MeasureTheory.Measure.haarScalarFactor_eq_mul haar (haar.map ψ hψ.aemeasurable),
    ← mulEquivHaarChar_eq (haar.map ψ hψ.aemeasurable)]

@[to_additive]
lemma mulEquivHaarChar_symm {φ : G ≃ₜ* G} :
    mulEquivHaarChar φ.symm = (mulEquivHaarChar φ)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  simp [← mulEquivHaarChar_trans]

open TopologicalSpace Set in
@[to_additive addEquivAddHaarChar_eq_one_of_compactSpace]
lemma mulEquivHaarChar_eq_one_of_compactSpace [CompactSpace G] (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ = 1 := by
  set μ := haarMeasure (⟨⟨univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts G)
  have hμ : μ univ = 1 := haarMeasure_self
  rw [mulEquivHaarChar_eq μ]
  suffices (μ.haarScalarFactor
      (map φ μ (map_continuous φ).measurable.aemeasurable) : ℝ≥0∞) = 1 by
    exact_mod_cast this
  calc
    _ = μ.haarScalarFactor (map φ μ (map_continuous φ).measurable.aemeasurable) •
        (1 : ℝ≥0∞) := by rw [ENNReal.smul_def, smul_eq_mul, mul_one]
    _ = μ.haarScalarFactor (map φ μ (map_continuous φ).measurable.aemeasurable) •
        (map φ μ (map_continuous φ).measurable.aemeasurable) univ := by
          rw [map_apply .univ (map_continuous φ).measurable.aemeasurable, Set.preimage_univ, hμ]
    _ = μ univ := by
          conv_rhs => rw [isMulInvariant_eq_smul_of_compactSpace μ
            (map φ μ (map_continuous φ).measurable.aemeasurable), Measure.smul_apply]
    _ = 1 := hμ

end MeasureTheory
