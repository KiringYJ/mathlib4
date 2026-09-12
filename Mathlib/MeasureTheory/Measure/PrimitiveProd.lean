/-
Copyright (c) 2026 KiringYJ. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KiringYJ
-/
module

public import Mathlib.MeasureTheory.Measure.ProductMeasure

/-!
# Fremlin's primitive product on the product sigma-algebra

The primitive product of two arbitrary measures is constructed by countable covers by measurable
rectangles. It is the greatest measure on the product sigma-algebra with the prescribed values on
measurable rectangles. No finiteness or measurability of section integrals is needed.

The name follows Fremlin's terminology in §251C and its notes, where he distinguishes his
primitive product from the complete locally determined product. This API restricts his
Carathéodory construction to the fixed product sigma-algebra; it does not claim that this
sigma-algebra is the full Carathéodory domain.

The underlying outer measure uses the same projection cost function as finite indexed products:
the cost of a set is the product of the outer measures of its two projections. Passing to
measurable hulls identifies this construction with measurable rectangle covers.

## References

* [Fremlin, *Measure Theory*, Volume 2, §251][fremlin_vol2]
-/

@[expose] public section

noncomputable section

open Set Function
open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*} [mα : SigmaAlgebra α] [mβ : SigmaAlgebra β]

namespace Measure

private def primitiveProdOuter (μ : Measure α) (ν : Measure β) : OuterMeasure (α × β) :=
  OuterMeasure.boundedBy fun s => μ (Prod.fst '' s) * ν (Prod.snd '' s)

private theorem primitiveProdOuter_prod_le (μ : Measure α) (ν : Measure β)
    (s : Set α) (t : Set β) : primitiveProdOuter μ ν (s ×ˢ t) ≤ μ s * ν t := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp
  exact (OuterMeasure.boundedBy_le _).trans_eq (by
    simp only [fst_image_prod _ ht, snd_image_prod hs])

private theorem primitiveProdOuter_caratheodory (μ : Measure α) (ν : Measure β) :
    mα.prod mβ ≤ (primitiveProdOuter μ ν).caratheodory := by
  refine sup_le ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    apply OuterMeasure.boundedBy_caratheodory
    intro t
    simp only [image_inter_preimage, image_sdiff_preimage]
    calc
      _ ≤ μ (Prod.fst '' t ∩ s) * ν (Prod.snd '' t) +
          μ (Prod.fst '' t \ s) * ν (Prod.snd '' t) := by
        gcongr
        · exact inter_subset_left
        · exact sdiff_subset
      _ = (μ (Prod.fst '' t ∩ s) + μ (Prod.fst '' t \ s)) * ν (Prod.snd '' t) :=
        (add_mul _ _ _).symm
      _ = _ := by rw [measure_inter_add_sdiff _ hs]
  · rintro _ ⟨s, hs, rfl⟩
    apply OuterMeasure.boundedBy_caratheodory
    intro t
    simp only [image_inter_preimage, image_sdiff_preimage]
    calc
      _ ≤ μ (Prod.fst '' t) * ν (Prod.snd '' t ∩ s) +
          μ (Prod.fst '' t) * ν (Prod.snd '' t \ s) := by
        gcongr
        · exact inter_subset_left
        · exact sdiff_subset
      _ = μ (Prod.fst '' t) * (ν (Prod.snd '' t ∩ s) + ν (Prod.snd '' t \ s)) :=
        (mul_add _ _ _).symm
      _ = _ := by rw [measure_inter_add_sdiff _ hs]

private theorem primitiveProdOuter_apply (μ : Measure α) (ν : Measure β) (u : Set (α × β)) :
    primitiveProdOuter μ ν u =
      ⨅ (s : ℕ → Set α) (t : ℕ → Set β) (_ : ∀ n, MeasurableSet (s n))
        (_ : ∀ n, MeasurableSet (t n)) (_ : u ⊆ ⋃ n, s n ×ˢ t n),
        ∑' n, μ (s n) * ν (t n) := by
  refine le_antisymm ?_ ?_
  · refine le_iInf fun s => le_iInf fun t => le_iInf fun _ => le_iInf fun _ =>
      le_iInf fun hu => ?_
    exact (measure_mono hu).trans ((measure_iUnion_le _).trans
      (ENNReal.tsum_le_tsum fun n => primitiveProdOuter_prod_le μ ν (s n) (t n)))
  · rw [primitiveProdOuter, OuterMeasure.boundedBy_eq_ofFunction (by simp),
      OuterMeasure.ofFunction_apply]
    refine le_iInf fun f => le_iInf fun hf => ?_
    refine iInf_le_of_le (fun n => toMeasurable μ (Prod.fst '' f n))
      (iInf_le_of_le (fun n => toMeasurable ν (Prod.snd '' f n))
        (iInf_le_of_le (fun n => measurableSet_toMeasurable μ _)
          (iInf_le_of_le (fun n => measurableSet_toMeasurable ν _) (iInf_le_of_le ?_ ?_))))
    · intro x hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hf hx)
      exact mem_iUnion.mpr ⟨n, subset_toMeasurable μ _ (mem_image_of_mem _ hn),
        subset_toMeasurable ν _ (mem_image_of_mem _ hn)⟩
    · simp only [measure_toMeasurable, le_refl]

/-- A rectangle cannot be covered by countably many measurable rectangles of smaller total cost.
This bound holds for arbitrary measures. -/
theorem mul_le_tsum_of_prod_subset_iUnion (μ : Measure α) (ν : Measure β)
    {s : Set α} {t : Set β} (hs : MeasurableSet s)
    (A : ℕ → Set α) (B : ℕ → Set β) (hA : ∀ n, MeasurableSet (A n))
    (hcover : s ×ˢ t ⊆ ⋃ n, A n ×ˢ B n) :
    μ s * ν t ≤ ∑' n, μ (A n) * ν (B n) := by
  classical
  have hpoint : s.indicator (fun _ => ν t) ≤
      fun x => ∑' n, (A n).indicator (fun _ => ν (B n)) x := by
    intro x
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx]
      calc
        ν t ≤ ν (⋃ n, if x ∈ A n then B n else ∅) := by
          apply measure_mono
          intro y hy
          obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover (show (x, y) ∈ s ×ˢ t from ⟨hx, hy⟩))
          exact mem_iUnion.mpr ⟨n, by simpa only [ite_eq_left hn.1] using hn.2⟩
        _ ≤ ∑' n, ν (if x ∈ A n then B n else ∅) := measure_iUnion_le _
        _ = _ := tsum_congr fun n => by
          by_cases hn : x ∈ A n <;> simp [hn]
    · simp only [indicator_of_notMem hx, zero_le]
  have hint := lintegral_mono (μ := μ) hpoint
  rw [lintegral_indicator_const hs, lintegral_tsum
    (fun n => (measurable_const.indicator (hA n)).aemeasurable)] at hint
  simpa only [lintegral_indicator_const (hA _), mul_comm] using hint

private theorem primitiveProdOuter_prod (μ : Measure α) (ν : Measure β)
    {s : Set α} {t : Set β} (hs : MeasurableSet s) :
    primitiveProdOuter μ ν (s ×ˢ t) = μ s * ν t := by
  refine (primitiveProdOuter_prod_le μ ν s t).antisymm ?_
  rw [primitiveProdOuter_apply]
  exact le_iInf fun A => le_iInf fun B => le_iInf fun hA => le_iInf fun _ =>
    le_iInf fun hcover => mul_le_tsum_of_prod_subset_iUnion μ ν hs A B hA hcover

/-- The primitive product measure, obtained from countable measurable rectangle covers.
It is the greatest product measure on the fixed product sigma-algebra. -/
@[no_expose] def primitiveProd (μ : Measure α) (ν : Measure β) : Measure (α × β) :=
  (primitiveProdOuter μ ν).toMeasure (primitiveProdOuter_caratheodory μ ν)

/-- The primitive product has the prescribed value on measurable rectangles. -/
@[simp]
theorem primitiveProd_prod (μ : Measure α) (ν : Measure β) {s : Set α} {t : Set β}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ.primitiveProd ν (s ×ˢ t) = μ s * ν t := by
  rw [primitiveProd, toMeasure_apply _ _ (hs.prod ht),
    primitiveProdOuter_prod μ ν hs]

/-- The primitive product satisfies the defining rectangle equations of a product measure. -/
theorem primitiveProd_isProductMeasure (μ : Measure α) (ν : Measure β) :
    IsProductMeasure μ ν (μ.primitiveProd ν) := fun _ _ hs ht => primitiveProd_prod μ ν hs ht

/-- The primitive product is the infimum of the costs of countable measurable rectangle covers.
The formula applies to every set, with the measure interpreted as its associated outer measure. -/
theorem primitiveProd_apply (μ : Measure α) (ν : Measure β) (u : Set (α × β)) :
    μ.primitiveProd ν u =
      ⨅ (s : ℕ → Set α) (t : ℕ → Set β) (_ : ∀ n, MeasurableSet (s n))
        (_ : ∀ n, MeasurableSet (t n)) (_ : u ⊆ ⋃ n, s n ×ˢ t n),
        ∑' n, μ (s n) * ν (t n) := by
  refine le_antisymm ?_ ?_
  · refine le_iInf fun s => le_iInf fun t => le_iInf fun hs => le_iInf fun ht =>
      le_iInf fun hu => ?_
    calc
      μ.primitiveProd ν u ≤ μ.primitiveProd ν (⋃ n, s n ×ˢ t n) := measure_mono hu
      _ ≤ ∑' n, μ.primitiveProd ν (s n ×ˢ t n) := measure_iUnion_le _
      _ = _ := tsum_congr fun n => primitiveProd_prod μ ν (hs n) (ht n)
  · rw [← primitiveProdOuter_apply]
    exact le_toMeasure_apply _ _ _

end Measure

/-- Every product measure is bounded above by the primitive product measure. -/
theorem IsProductMeasure.le_primitiveProd {μ : Measure α} {ν : Measure β}
    {ρ : Measure (α × β)} (hρ : IsProductMeasure μ ν ρ) : ρ ≤ μ.primitiveProd ν := by
  intro u
  rw [Measure.primitiveProd_apply]
  refine le_iInf fun s => le_iInf fun t => le_iInf fun hs => le_iInf fun ht =>
    le_iInf fun hu => ?_
  calc
    ρ u ≤ ρ (⋃ n, s n ×ˢ t n) := measure_mono hu
    _ ≤ ∑' n, ρ (s n ×ˢ t n) := measure_iUnion_le _
    _ = _ := tsum_congr fun n => hρ (hs n) (ht n)

namespace Measure

/-- Swapping the coordinates interchanges the factors of the primitive product. -/
@[simp]
theorem primitiveProd_swap (μ : Measure α) (ν : Measure β) :
    (μ.primitiveProd ν).map Prod.swap measurable_swap.aemeasurable = ν.primitiveProd μ := by
  refine (primitiveProd_isProductMeasure μ ν).swap.le_primitiveProd.antisymm ?_
  have h := map_mono (primitiveProd_isProductMeasure ν μ).swap.le_primitiveProd
    (measurable_swap : Measurable (Prod.swap : α × β → β × α))
  simpa only [map_map measurable_swap.aemeasurable measurable_swap.aemeasurable,
    Prod.swap_swap_eq, map_id] using h

end Measure

end MeasureTheory
