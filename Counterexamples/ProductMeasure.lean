/-
Copyright (c) 2026 KiringYJ. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KiringYJ
-/
module

public import Mathlib.MeasureTheory.Measure.PrimitiveProd
public import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# Nonuniqueness of products of s-finite measures

Let `infiniteLebesgue` be infinity times Lebesgue measure on the real line. This measure is
s-finite, as it is a countable sum of copies of Lebesgue measure. Its product defined by section
integrals with itself gives the diagonal measure zero, since every singleton has measure zero.

Adding Lebesgue measure pushed forward along the diagonal produces a different measure with
the same values on measurable rectangles. Indeed, the additional measure vanishes whenever
either side of the rectangle is null, and otherwise the rectangle already has infinite measure.
Consequently, s-finite factors need not satisfy `MeasureTheory.HasUniqueProduct`.
The primitive product has infinite mass on the diagonal by its maximality among product
measures, so it also differs from the product defined by section integrals for this pair of
s-finite factors.

We use the Stieltjes construction of Lebesgue measure to keep the imports independent of the
higher-dimensional Lebesgue measure API.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Counterexample.ProductMeasure

/-- Infinity times Lebesgue measure on the real line. -/
def infiniteLebesgue : Measure ℝ := ∞ • StieltjesFunction.id.measure

lemma infiniteLebesgue_eq_sum :
    infiniteLebesgue = Measure.sum (fun _ : ℕ => StieltjesFunction.id.measure) := by
  ext s hs
  by_cases h : StieltjesFunction.id.measure s = 0 <;>
    simp [infiniteLebesgue, Measure.sum_apply _ hs, h]

instance : SFinite infiniteLebesgue := by
  rw [infiniteLebesgue_eq_sum]
  infer_instance

@[simp]
lemma infiniteLebesgue_singleton (x : ℝ) : infiniteLebesgue {x} = 0 := by
  simp [infiniteLebesgue, StieltjesFunction.measure_singleton]

/-- Lebesgue measure pushed forward along the diagonal. -/
def diagonalLebesgue : Measure (ℝ × ℝ) :=
  StieltjesFunction.id.measure.map (fun x => (x, x))
    (measurable_id.prodMk measurable_id).aemeasurable

lemma diagonalLebesgue_diagonal : diagonalLebesgue (diagonal ℝ) = ∞ := by
  rw [diagonalLebesgue, Measure.map_apply measurableSet_diagonal]
  have h : (fun x : ℝ => (x, x)) ⁻¹' diagonal ℝ = univ := by ext x; simp
  rw [h]
  exact StieltjesFunction.id.measure_univ_of_tendsto_atTop_atTop Filter.tendsto_id

lemma diagonalLebesgue_prod {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    diagonalLebesgue (s ×ˢ t) = StieltjesFunction.id.measure (s ∩ t) := by
  rw [diagonalLebesgue, Measure.map_apply (hs.prod ht)]
  rfl

lemma productBySections_infiniteLebesgue_diagonal :
    (infiniteLebesgue.productBySections infiniteLebesgue) (diagonal ℝ) = 0 := by
  rw [Measure.productBySections_apply measurableSet_diagonal]
  have h (x : ℝ) : Prod.mk x ⁻¹' diagonal ℝ = {x} := by
    ext y
    simp [Set.diagonal, eq_comm]
  simp [h]

lemma isProductMeasure_productBySections_add_diagonalLebesgue :
    IsProductMeasure infiniteLebesgue infiniteLebesgue
      (infiniteLebesgue.productBySections infiniteLebesgue + diagonalLebesgue) := by
  intro s t hs ht
  have hprod := Measure.productBySections_isProductMeasure infiniteLebesgue infiniteLebesgue
  rw [Measure.add_apply, hprod hs ht, diagonalLebesgue_prod hs ht]
  by_cases hs0 : StieltjesFunction.id.measure s = 0
  · have hst : StieltjesFunction.id.measure (s ∩ t) = 0 :=
      measure_mono_null inter_subset_left hs0
    simp [infiniteLebesgue, hs0, hst]
  by_cases ht0 : StieltjesFunction.id.measure t = 0
  · have hst : StieltjesFunction.id.measure (s ∩ t) = 0 :=
      measure_mono_null inter_subset_right ht0
    simp [infiniteLebesgue, ht0, hst]
  simp [infiniteLebesgue, hs0, ht0]

lemma productBySections_ne_add_diagonalLebesgue :
    infiniteLebesgue.productBySections infiniteLebesgue ≠
      infiniteLebesgue.productBySections infiniteLebesgue + diagonalLebesgue := by
  intro h
  have hdiag := congrArg (fun ρ : Measure (ℝ × ℝ) => ρ (diagonal ℝ)) h
  simp [Measure.add_apply, productBySections_infiniteLebesgue_diagonal,
    diagonalLebesgue_diagonal] at hdiag

/-- S-finiteness of both factors does not imply uniqueness of a product measure. -/
theorem not_hasUniqueProduct_infiniteLebesgue :
    ¬ HasUniqueProduct infiniteLebesgue infiniteLebesgue := by
  rintro ⟨ρ, -, huniq⟩
  exact productBySections_ne_add_diagonalLebesgue
    ((huniq _ (Measure.productBySections_isProductMeasure _ _)).trans
      (huniq _ isProductMeasure_productBySections_add_diagonalLebesgue).symm)

lemma primitiveProd_infiniteLebesgue_diagonal :
    infiniteLebesgue.primitiveProd infiniteLebesgue (diagonal ℝ) = ∞ := by
  apply top_unique
  have h := isProductMeasure_productBySections_add_diagonalLebesgue.le_primitiveProd (diagonal ℝ)
  simpa [Measure.add_apply, productBySections_infiniteLebesgue_diagonal,
    diagonalLebesgue_diagonal] using h

/-- The primitive product and the product defined by section integrals need not agree for s-finite
factors. -/
theorem primitiveProd_ne_productBySections_infiniteLebesgue :
    infiniteLebesgue.primitiveProd infiniteLebesgue ≠
      infiniteLebesgue.productBySections infiniteLebesgue := by
  intro h
  have hdiag := congrArg (fun ρ : Measure (ℝ × ℝ) => ρ (diagonal ℝ)) h
  simp [primitiveProd_infiniteLebesgue_diagonal,
    productBySections_infiniteLebesgue_diagonal] at hdiag

end Counterexample.ProductMeasure
