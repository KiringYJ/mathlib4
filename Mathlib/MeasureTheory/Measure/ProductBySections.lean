/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Measure.ProductMeasure
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Doubling

/-!
# Product measures by section integrals

`productBySections` is a descriptive API name for construction by section integrals, not a claim
that "iterated product measure" is an established name for this binary construction.

This file develops the ordered section-integral construction `Measure.productBySections`. If `α` and
`β` have s-finite measures `μ` resp. `ν` then `α × β` can be equipped with an s-finite measure
`μ.productBySections ν`. For measurable `s`, it satisfies
`(μ.productBySections ν) s = ∫⁻ x, ν {y | (x, y) ∈ s} ∂μ`.
We also have `(μ.productBySections ν) (s ×ˢ t) = μ s * ν t`, i.e. the measure of a rectangle is the
product of the measures of the sides.

We also prove Tonelli's theorem. These results concern the iterated construction;
s-finiteness does not assert uniqueness from rectangle values. The ordinary
`Measure.prod` requires `HasUniqueProduct` and is developed in `Measure.UniqueProd`.

This construction does not install a global product `MeasureSpace` instance. Use
`MeasureSpace.productBySections` explicitly to select it as a local ambient measure.
The canonical sigma-finite product instance is provided by `Measure.UniqueProd`.

## Main definition

* `MeasureTheory.Measure.productBySections`: The measure constructed by integrating section
  measures.

## Main results

* `MeasureTheory.Measure.productBySections_apply` states
  `(μ.productBySections ν) s = ∫⁻ x, ν {y | (x, y) ∈ s} ∂μ` for measurable `s`.
  `MeasureTheory.Measure.productBySections_apply_symm` is the reversed version.
* `MeasureTheory.Measure.productBySections_prod` states
  `(μ.productBySections ν) (s ×ˢ t) = μ s * ν t` for measurable sets `s` and `t`.
* `MeasureTheory.lintegral_productBySections`: Tonelli's theorem. For a measurable function
  `α × β → ℝ≥0∞` we have `∫⁻ z, f z ∂(μ.productBySections ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ`.
  The version
  for functions `α → β → ℝ≥0∞` is reversed, and called `lintegral_lintegral`. Both versions have
  a variant with `_symm` appended, where the order of integration is reversed.
  The lemma `Measurable.lintegral_prod_right'` states that the inner integral of the right-hand side
  is measurable.

## Implementation Notes

Many results are proven twice, once for functions in curried form (`α → β → γ`) and one for
functions in uncurried form (`α × β → γ`). The former often has an assumption
`Measurable (uncurry f)`, which could be inconvenient to discharge, but for the latter it is more
common that the function has to be given explicitly, since Lean cannot synthesize the function by
itself. We name the lemmas about the uncurried form with a prime.
Tonelli's theorem has a different naming scheme, since the version for the uncurried version is
reversed.

## References

* [Vákár and Ong, *On S-Finite Measures and Kernels*, §4](https://arxiv.org/html/1810.01837)
  discusses products defined by iterated integration and the distinction from maximal products.

## Tags

product measure, Tonelli's theorem, Fubini-Tonelli theorem
-/

@[expose] public section


noncomputable section

open ENNReal MeasureTheory Set Function Real ENNReal SigmaAlgebra MeasureTheory.Measure

open TopologicalSpace hiding generateFrom

open Filter hiding prod_eq map

variable {α β γ : Type*}

variable [SigmaAlgebra α] [SigmaAlgebra β] [SigmaAlgebra γ]
variable {μ μ' : Measure α} {ν ν' : Measure β} {τ : Measure γ}

/-! ### The product defined by section integrals -/


namespace MeasureTheory

namespace Measure

/-- Equip a product with the measure defined by section integrals. This is an explicit
constructor, not a global instance; use `letI` when selecting this ambient measure. -/
@[instance_reducible]
def _root_.MeasureTheory.MeasureSpace.productBySections (α β) [MeasureSpace α] [MeasureSpace β]
    (h : HasAEMeasurableSectionMeasures (volume : Measure α) (volume : Measure β) := by
      first
      | assumption
      | exact MeasureTheory.hasAEMeasurableSectionMeasures_zero_left _
      | exact MeasureTheory.hasAEMeasurableSectionMeasures_of_sfinite _ _) :
    MeasureSpace (α × β) where
  volume := volume.productBySections volume h

/-- The iterated measure is bounded by its section integral on measurable sets. -/
theorem productBySections_apply_le {s : Set (α × β)} (hs : MeasurableSet s)
    (h : HasAEMeasurableSectionMeasures μ ν := by
      first | assumption | exact MeasureTheory.hasAEMeasurableSectionMeasures_of_sfinite _ _) :
    (μ.productBySections ν h) s ≤ ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ :=
  (productBySections_apply hs h).le

variable [SFinite ν]

/-- The iterated measure of a rectangle is bounded by the product of its side measures.
The sets need not be measurable. See `productBySections_prod` below for equality. -/
theorem productBySections_prod_le (s : Set α) (t : Set β) :
    (μ.productBySections ν) (s ×ˢ t) ≤ μ s * ν t := by
  set S := toMeasurable μ s
  set T := toMeasurable ν t
  calc
    (μ.productBySections ν) (s ×ˢ t) ≤ (μ.productBySections ν) (S ×ˢ T) := by
      gcongr <;> apply subset_toMeasurable
    _ ≤ ∫⁻ x, ν (Prod.mk x ⁻¹' (S ×ˢ T)) ∂μ := productBySections_apply_le (by measurability)
    _ = μ S * ν T := by
      classical
      simp_rw [S, mk_preimage_prod_right_eq_if, measure_if,
        lintegral_indicator (measurableSet_toMeasurable _ _), lintegral_const,
        restrict_apply_univ, mul_comm]
    _ = μ s * ν t := by rw [measure_toMeasurable, measure_toMeasurable]

instance productBySections.instNullSingletonClass_fst [NullSingletonClass μ] :
    NullSingletonClass (Measure.productBySections μ ν) where
  measure_singleton
  | (x, y) => nonpos_iff_eq_zero.mp <| calc
    (μ.productBySections ν) {(x, y)} = (μ.productBySections ν) ({x} ×ˢ {y}) := by
      rw [singleton_prod_singleton]
    _ ≤ μ {x} * ν {y} := productBySections_prod_le _ _
    _ = 0 := by simp

instance productBySections.instNullSingletonClass_snd [NullSingletonClass ν] :
    NullSingletonClass (Measure.productBySections μ ν) where
  measure_singleton
  | (x, y) => nonpos_iff_eq_zero.mp <| calc
    (μ.productBySections ν) {(x, y)} = (μ.productBySections ν) ({x} ×ˢ {y}) := by
      rw [singleton_prod_singleton]
    _ ≤ μ {x} * ν {y} := productBySections_prod_le _ _
    _ = 0 := by simp

/-- The product measure of the product of two sets is the product of their measures. Note that we
do not need the sets to be measurable. -/
@[simp]
theorem productBySections_prod (s : Set α) (t : Set β) :
    (μ.productBySections ν) (s ×ˢ t) = μ s * ν t := by
  apply (productBySections_prod_le s t).antisymm
  -- Formalization is based on https://mathoverflow.net/a/254134/136589
  set ST := toMeasurable (μ.productBySections ν) (s ×ˢ t)
  have hSTm : MeasurableSet ST := measurableSet_toMeasurable _ _
  have hST : s ×ˢ t ⊆ ST := subset_toMeasurable _ _
  set f : α → ℝ≥0∞ := fun x => ν (Prod.mk x ⁻¹' ST)
  have hfm : Measurable f := measurable_measure_prodMk_left hSTm
  set s' : Set α := { x | ν t ≤ f x }
  have hss' : s ⊆ s' := fun x hx => measure_mono fun y hy => hST <| mk_mem_prod hx hy
  calc
    μ s * ν t ≤ μ s' * ν t := by gcongr
    _ = ∫⁻ _ in s', ν t ∂μ := by rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ x in s', f x ∂μ := setLIntegral_mono hfm fun x => id
    _ ≤ ∫⁻ x, f x ∂μ := lintegral_mono' restrict_le_self le_rfl
    _ = (μ.productBySections ν) ST := (productBySections_apply hSTm).symm
    _ = (μ.productBySections ν) (s ×ˢ t) := measure_toMeasurable _

@[simp]
theorem _root_.MeasureTheory.measureReal_productBySections_prod (s : Set α) (t : Set β) :
    (μ.productBySections ν).real (s ×ˢ t) = μ.real s * ν.real t := by
  simp only [measureReal_def, productBySections_prod, ENNReal.toReal_mul]

@[simp] lemma map_fst_productBySections :
    Measure.map Prod.fst (μ.productBySections ν) measurable_fst.aemeasurable = (ν univ) • μ := by
  ext s hs
  simp [Measure.map_apply hs measurable_fst.aemeasurable, ← prod_univ, mul_comm]

lemma _root_.MeasureTheory.measurePreserving_fst [IsProbabilityMeasure ν] :
    MeasurePreserving Prod.fst (μ.productBySections ν) μ :=
  ⟨measurable_fst, by rw [map_fst_productBySections, measure_univ, one_smul]⟩

@[simp] lemma map_snd_productBySections :
    Measure.map Prod.snd (μ.productBySections ν) measurable_snd.aemeasurable = (μ univ) • ν := by
  ext s hs
  simp [Measure.map_apply hs measurable_snd.aemeasurable, ← univ_prod]

lemma _root_.MeasureTheory.measurePreserving_snd [IsProbabilityMeasure μ] :
    MeasurePreserving Prod.snd (μ.productBySections ν) ν :=
  ⟨measurable_snd, by rw [map_snd_productBySections, measure_univ, one_smul]⟩

instance productBySections.instIsOpenPosMeasure {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y]
    {m : SigmaAlgebra X} {μ : Measure X} [IsOpenPosMeasure μ] {m' : SigmaAlgebra Y}
    {ν : Measure Y} [IsOpenPosMeasure ν] [SFinite ν] :
    IsOpenPosMeasure (μ.productBySections ν) := by
  constructor
  rintro U U_open ⟨⟨x, y⟩, hxy⟩
  rcases isOpen_prod_iff.1 U_open x y hxy with ⟨u, v, u_open, v_open, xu, yv, huv⟩
  refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono huv))
  simp only [productBySections_prod, CanonicallyOrderedAdd.mul_pos]
  constructor
  · exact u_open.measure_pos μ ⟨x, xu⟩
  · exact v_open.measure_pos ν ⟨y, yv⟩

protected theorem FiniteAtFilter.prod {X Y : Type*} {m : SigmaAlgebra X} {μ : Measure X}
    {m' : SigmaAlgebra Y} {ν : Measure Y} [SFinite ν] {l : Filter X} {l' : Filter Y}
    (hμ : μ.FiniteAtFilter l) (hν : ν.FiniteAtFilter l') :
    (μ.productBySections ν).FiniteAtFilter (l ×ˢ l') := by
  rcases hμ with ⟨s, hs, hμs⟩
  rcases hν with ⟨t, ht, hνt⟩
  use s ×ˢ t, Filter.prod_mem_prod hs ht
  grw [productBySections_prod_le]
  exact ENNReal.mul_lt_top hμs hνt

instance productBySections.instIsLocallyFiniteMeasure {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {m : SigmaAlgebra X} {μ : Measure X} [IsLocallyFiniteMeasure μ] {m' : SigmaAlgebra Y}
    {ν : Measure Y} [SFinite ν] [IsLocallyFiniteMeasure ν] :
    IsLocallyFiniteMeasure (μ.productBySections ν) where
  finiteAtNhds x := by
    rw [nhds_prod_eq]
    exact μ.finiteAt_nhds _ |>.prod <| ν.finiteAt_nhds _

instance productBySections.instIsFiniteMeasure {α β : Type*} {mα : SigmaAlgebra α}
    {mβ : SigmaAlgebra β}
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsFiniteMeasure (μ.productBySections ν) := by
  constructor
  rw [← univ_prod_univ, productBySections_prod]
  finiteness

instance productBySections.instIsProbabilityMeasure {α β : Type*} {mα : SigmaAlgebra α}
    {mβ : SigmaAlgebra β} (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (μ.productBySections ν) :=
  ⟨by rw [← univ_prod_univ, productBySections_prod, measure_univ, measure_univ, mul_one]⟩

instance productBySections.instIsFiniteMeasureOnCompacts {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β]
    {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β} (μ : Measure α) (ν : Measure β) [SFinite ν]
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] :
    IsFiniteMeasureOnCompacts (μ.productBySections ν) where
  lt_top_of_isCompact K hK := calc
    (μ.productBySections ν) K ≤ (μ.productBySections ν) ((Prod.fst '' K) ×ˢ (Prod.snd '' K)) :=
      measure_mono subset_prod
    _ ≤ μ (Prod.fst '' K) * ν (Prod.snd '' K) := productBySections_prod_le _ _
    _ < ∞ :=
      mul_lt_top (hK.image continuous_fst).measure_lt_top (hK.image continuous_snd).measure_lt_top


open IsUnifLocDoublingMeasure in
/--
The product of two uniformly locally doubling measures is a uniformly locally doubling measure,
assuming the second one is s-finite.
-/
instance _root_.IsUnifLocDoublingMeasure.prod {X Y : Type*}
    [PseudoMetricSpace X] [SigmaAlgebra X] [PseudoMetricSpace Y] [SigmaAlgebra Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    [IsUnifLocDoublingMeasure μ] [IsUnifLocDoublingMeasure ν] :
    IsUnifLocDoublingMeasure (μ.productBySections ν) := by
  constructor
  use doublingConstant μ * doublingConstant ν
  filter_upwards [eventually_measure_le_doublingConstant_mul μ,
    eventually_measure_le_doublingConstant_mul ν] with r hμr hνr x
  rw [← closedBall_prod_same, productBySections_prod, ← closedBall_prod_same,
    productBySections_prod]
  grw [hμr, hνr, ENNReal.coe_mul, mul_mul_mul_comm]

theorem ae_measure_lt_top {s : Set (α × β)} (hs : MeasurableSet s)
    (h2s : (μ.productBySections ν) s ≠ ∞) :
    ∀ᵐ x ∂μ, ν (Prod.mk x ⁻¹' s) < ∞ := by
  rw [productBySections_apply hs] at h2s
  exact ae_lt_top (measurable_measure_prodMk_left hs) h2s

omit [SFinite ν] in
/-- If `μ`-a.e. section `{y | (x, y) ∈ s}` of a measurable set have `ν` measure zero,
then `s` has `μ.productBySections ν` measure zero.

This implication requires `s` to be measurable but does not require `ν` to be s-finite.
See also `measure_prod_null` and `measure_ae_null_of_prod_null` below. -/
theorem measure_prod_null_of_ae_null {s : Set (α × β)} (hsm : MeasurableSet s)
    (hs : (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0)
    (hprod : HasAEMeasurableSectionMeasures μ ν := by
      first | assumption | exact MeasureTheory.hasAEMeasurableSectionMeasures_of_sfinite _ _) :
    (μ.productBySections ν hprod) s = 0 := by
  rw [← nonpos_iff_eq_zero]
  calc
    (μ.productBySections ν hprod) s ≤ ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ :=
      productBySections_apply_le hsm hprod
    _ = 0 := by simp [lintegral_congr_ae hs]

/-- A measurable set `s` has `μ.productBySections ν` measure zero, where `ν` is an s-finite measure,
if and only if `μ`-a.e. section `{y | (x, y) ∈ s}` of `s` have `ν` measure zero.

See `measure_ae_null_of_prod_null` for the forward implication without the measurability assumption
and `measure_prod_null_of_ae_null` for the reverse implication without the s-finiteness assumption.

Note: the assumption `hs` cannot be dropped. For a counterexample, see
Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9. -/
theorem measure_prod_null {s : Set (α × β)} (hs : MeasurableSet s) :
    (μ.productBySections ν) s = 0 ↔ (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0 := by
  rw [productBySections_apply hs, lintegral_eq_zero_iff (measurable_measure_prodMk_left hs)]

/-- Note: the converse is not true without assuming that `s` is measurable. For a counterexample,
  see Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9. -/
theorem measure_ae_null_of_prod_null {s : Set (α × β)} (h : (μ.productBySections ν) s = 0) :
    (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0 := by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  rw [measure_prod_null mt] at ht
  rw [eventuallyLE_antisymm_iff]
  exact
    ⟨EventuallyLE.trans_eq (Eventually.of_forall fun x => measure_mono (preimage_mono hst)) ht,
      Eventually.of_forall fun x => zero_le⟩

theorem AbsolutelyContinuous.prod [SFinite ν'] (h1 : μ ≪ μ') (h2 : ν ≪ ν') :
    μ.productBySections ν ≪ μ'.productBySections ν' := by
  refine AbsolutelyContinuous.mk fun s hs h2s => ?_
  apply measure_prod_null_of_ae_null hs
  rw [measure_prod_null hs] at h2s
  exact (h2s.filter_mono h1.ae_le).mono fun _ h => h2 h

@[gcongr] theorem productBySections_mono [SFinite ν'] (h1 : μ ≤ μ') (h2 : ν ≤ ν') :
    μ.productBySections ν ≤ μ'.productBySections ν' := by
  apply Measure.le_iff.2 (fun s hs ↦ ?_)
  calc (μ.productBySections ν) s
  _ ≤ ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ := productBySections_apply_le hs
  _ ≤ ∫⁻ x, ν' (Prod.mk x ⁻¹' s) ∂μ' := by gcongr
  _ = (μ'.productBySections ν') s := (productBySections_apply hs).symm

/-- Note: the converse is not true. For a counterexample, see
  Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9. It is true if the set is
  measurable, see `ae_prod_mem_iff_ae_ae_mem`. -/
theorem ae_ae_of_ae_prod {p : α × β → Prop} (h : ∀ᵐ z ∂μ.productBySections ν, p z) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, p (x, y) :=
  measure_ae_null_of_prod_null h

theorem ae_ae_eq_curry_of_prod {γ : Type*} {f g : α × β → γ} (h : f =ᵐ[μ.productBySections ν] g) :
    ∀ᵐ x ∂μ, curry f x =ᵐ[ν] curry g x :=
  ae_ae_of_ae_prod h

theorem ae_ae_eq_of_ae_eq_uncurry {γ : Type*} {f g : α → β → γ}
    (h : uncurry f =ᵐ[μ.productBySections ν] uncurry g) : ∀ᵐ x ∂μ, f x =ᵐ[ν] g x :=
  ae_ae_eq_curry_of_prod h

theorem ae_prod_iff_ae_ae {p : α × β → Prop} (hp : MeasurableSet {x | p x}) :
    (∀ᵐ z ∂μ.productBySections ν, p z) ↔ ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, p (x, y) :=
  measure_prod_null hp.compl

theorem ae_prod_mem_iff_ae_ae_mem {s : Set (α × β)} (hs : MeasurableSet s) :
    (∀ᵐ z ∂μ.productBySections ν, z ∈ s) ↔ ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, (x, y) ∈ s :=
  measure_prod_null hs.compl

/-- Version of `productBySections_apply` for a null measurable set. -/
theorem productBySections_apply₀ {s : Set (α × β)}
    (hs : NullMeasurableSet s (μ.productBySections ν)) :
    (μ.productBySections ν) s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ := by
  obtain ⟨t, htm, hst⟩ := hs
  rw [measure_congr hst, productBySections_apply htm]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_ae_of_ae_prod hst] with x hx
  exact (measure_congr hx).symm

@[fun_prop]
theorem quasiMeasurePreserving_fst : QuasiMeasurePreserving Prod.fst (μ.productBySections ν) μ := by
  refine ⟨measurable_fst, AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
  rw [map_apply hs measurable_fst.aemeasurable, ← prod_univ, ← nonpos_iff_eq_zero]
  refine (productBySections_prod_le _ _).trans_eq ?_
  rw [h2s, zero_mul]

@[fun_prop]
theorem quasiMeasurePreserving_snd : QuasiMeasurePreserving Prod.snd (μ.productBySections ν) ν := by
  refine ⟨measurable_snd, AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
  rw [map_apply hs measurable_snd.aemeasurable, ← univ_prod, ← nonpos_iff_eq_zero]
  refine (productBySections_prod_le _ _).trans_eq ?_
  rw [h2s, mul_zero]

lemma set_prod_ae_eq {s s' : Set α} {t t' : Set β} (hs : s =ᵐ[μ] s') (ht : t =ᵐ[ν] t') :
    (s ×ˢ t : Set (α × β)) =ᵐ[μ.productBySections ν] (s' ×ˢ t' : Set (α × β)) :=
  (quasiMeasurePreserving_fst.preimage_ae_eq hs).inter
    (quasiMeasurePreserving_snd.preimage_ae_eq ht)

lemma measure_prod_compl_eq_zero {s : Set α} {t : Set β}
    (s_ae_univ : μ sᶜ = 0) (t_ae_univ : ν tᶜ = 0) :
    (μ.productBySections ν) (s ×ˢ t)ᶜ = 0 := by
  rw [Set.compl_prod_eq_union, measure_union_null_iff]
  simp [s_ae_univ, t_ae_univ]

lemma _root_.MeasureTheory.NullMeasurableSet.prod {s : Set α} {t : Set β}
    (s_mble : NullMeasurableSet s μ) (t_mble : NullMeasurableSet t ν) :
    NullMeasurableSet (s ×ˢ t) (μ.productBySections ν) :=
  let ⟨s₀, mble_s₀, s_aeeq_s₀⟩ := s_mble
  let ⟨t₀, mble_t₀, t_aeeq_t₀⟩ := t_mble
  ⟨s₀ ×ˢ t₀, ⟨MeasurableSet.prod mble_s₀ mble_t₀, set_prod_ae_eq s_aeeq_s₀ t_aeeq_t₀⟩⟩

/-- If `s ×ˢ t` is a null measurable set and `μ s ≠ 0`, then `t` is a null measurable set. -/
lemma _root_.MeasureTheory.NullMeasurableSet.right_of_prod {s : Set α} {t : Set β}
    (h : NullMeasurableSet (s ×ˢ t) (μ.productBySections ν)) (hs : μ s ≠ 0) :
    NullMeasurableSet t ν := by
  rcases h with ⟨u, hum, hu⟩
  obtain ⟨x, hxs, hx⟩ : ∃ x ∈ s, (Prod.mk x ⁻¹' (s ×ˢ t)) =ᵐ[ν] (Prod.mk x ⁻¹' u) :=
    ((frequently_ae_iff.2 hs).and_eventually (ae_ae_eq_curry_of_prod hu)).exists
  refine ⟨Prod.mk x ⁻¹' u, measurable_prodMk_left hum, ?_⟩
  rwa [mk_preimage_prod_right hxs] at hx

/-- If `Prod.snd ⁻¹' t` is a null measurable set and `μ ≠ 0`, then `t` is a null measurable set. -/
lemma _root_.MeasureTheory.NullMeasurableSet.of_preimage_snd [NeZero μ] {t : Set β}
    (h : NullMeasurableSet (Prod.snd ⁻¹' t) (μ.productBySections ν)) : NullMeasurableSet t ν :=
  .right_of_prod (by rwa [univ_prod]) (NeZero.ne (μ univ))

/-- `Prod.snd ⁻¹' t` is null measurable w.r.t. `μ.productBySections ν` iff `t` is null measurable
w.r.t. `ν`
provided that `μ ≠ 0`. -/
lemma nullMeasurableSet_preimage_snd [NeZero μ] {t : Set β} :
    NullMeasurableSet (Prod.snd ⁻¹' t) (μ.productBySections ν) ↔ NullMeasurableSet t ν :=
  ⟨.of_preimage_snd, (.preimage · quasiMeasurePreserving_snd)⟩

lemma nullMeasurable_comp_snd [NeZero μ] {f : β → γ} :
    NullMeasurable (f ∘ Prod.snd) (μ.productBySections ν) ↔ NullMeasurable f ν :=
  forall₂_congr fun s _ ↦ nullMeasurableSet_preimage_snd (t := f ⁻¹' s)

/-- `μ.productBySections ν` has finite spanning sets in rectangles of finite spanning sets. -/
noncomputable def FiniteSpanningSetsIn.prod {ν : Measure β} {C : Set (Set α)} {D : Set (Set β)}
    (hμ : μ.FiniteSpanningSetsIn C) (hν : ν.FiniteSpanningSetsIn D) :
    (μ.productBySections ν (by
      let _ : SigmaFinite ν := hν.sigmaFinite
      exact MeasureTheory.hasAEMeasurableSectionMeasures_of_sfinite _ _)).FiniteSpanningSetsIn
        (image2 (· ×ˢ ·) C D) := by
  let _ : SigmaFinite ν := hν.sigmaFinite
  refine
    ⟨fun n => hμ.set n.unpair.1 ×ˢ hν.set n.unpair.2, fun n =>
      mem_image2_of_mem (hμ.set_mem _) (hν.set_mem _), fun n => ?_, ?_⟩
  · rw [productBySections_prod]
    exact mul_lt_top (hμ.finite _) (hν.finite _)
  · simp_rw [iUnion_unpair_prod, hμ.spanning, hν.spanning, univ_prod_univ]

lemma productBySections_sum_left {ι : Type*} (m : ι → Measure α) (μ : Measure β) [SFinite μ] :
    (Measure.sum m).productBySections μ = Measure.sum (fun i ↦ (m i).productBySections μ) := by
  ext s hs
  simp only [productBySections_apply,
    lintegral_sum_measure, hs, sum_apply]

lemma productBySections_sum_right {ι' : Type*} [Countable ι'] (m : Measure α) (m' : ι' → Measure β)
    [∀ n, SFinite (m' n)] :
    m.productBySections (Measure.sum m') = Measure.sum (fun p ↦ m.productBySections (m' p)) := by
  ext s hs
  simp only [productBySections_apply, hs, sum_apply]
  have M : ∀ x, MeasurableSet (Prod.mk x ⁻¹' s) := fun x => measurable_prodMk_left hs
  simp_rw [Measure.sum_apply _ (M _)]
  rw [lintegral_tsum (fun i ↦ (measurable_measure_prodMk_left hs).aemeasurable)]

lemma productBySections_sum {ι ι' : Type*} [Countable ι'] (m : ι → Measure α) (m' : ι' → Measure β)
    [∀ n, SFinite (m' n)] :
    (Measure.sum m).productBySections (Measure.sum m') =
      Measure.sum (fun (p : ι × ι') ↦ (m p.1).productBySections (m' p.2)) := by
  simp_rw [productBySections_sum_left, productBySections_sum_right, sum_sum]

instance productBySections.instSigmaFinite {α β : Type*} {_ : SigmaAlgebra α} {μ : Measure α}
    [SigmaFinite μ] {_ : SigmaAlgebra β} {ν : Measure β} [SigmaFinite ν] :
    SigmaFinite (μ.productBySections ν) :=
  (μ.toFiniteSpanningSetsIn.prod ν.toFiniteSpanningSetsIn).sigmaFinite

instance productBySections.instSFinite {α β : Type*} {_ : SigmaAlgebra α} {μ : Measure α}
    [SFinite μ] {_ : SigmaAlgebra β} {ν : Measure β} [SFinite ν] :
    SFinite (μ.productBySections ν) := by
  have : μ.productBySections ν =
      Measure.sum (fun (p : ℕ × ℕ) ↦ (sfiniteSeq μ p.1).productBySections (sfiniteSeq ν p.2)) := by
    simpa only [sum_sfiniteSeq] using productBySections_sum (sfiniteSeq μ) (sfiniteSeq ν)
  rw [this]
  infer_instance

/-- A measure on a product space equals the product measure if they are equal on rectangles
  with as sides sets that generate the corresponding σ-algebras. -/
theorem productBySections_eq_generateFrom {μ : Measure α} {ν : Measure β}
    {C : Set (Set α)} {D : Set (Set β)}
    (hC : generateFrom C = ‹_›) (hD : generateFrom D = ‹_›) (h2C : IsPiSystem C)
    (h2D : IsPiSystem D) (h3C : μ.FiniteSpanningSetsIn C) (h3D : ν.FiniteSpanningSetsIn D)
    {μν : Measure (α × β)}
    (h₁ : ∀ s ∈ C, ∀ t ∈ D, μν (s ×ˢ t) = μ s * ν t) :
    μ.productBySections ν (by
      let _ : SigmaFinite ν := h3D.sigmaFinite
      exact MeasureTheory.hasAEMeasurableSectionMeasures_of_sfinite _ _) = μν := by
  let _ : SigmaFinite ν := h3D.sigmaFinite
  refine
    (h3C.prod h3D).ext
      (generateFrom_eq_prod hC hD h3C.isCountablySpanning h3D.isCountablySpanning).symm
      (h2C.prod h2D) ?_
  rintro _ ⟨s, hs, t, ht, rfl⟩
  have := h3D.sigmaFinite
  rw [h₁ s hs t ht, productBySections_prod]

/- Note that the next theorem is not true for s-finite measures: let `μ = ν = ∞ • Leb` on `[0,1]`
(they are s-finite as countable sums of the finite Lebesgue measure), and let
`μν = μ.productBySections ν + λ`
where `λ` is Lebesgue measure on the diagonal. Then both measures give infinite mass to rectangles
`s × t` whose sides have positive Lebesgue measure, and `0` measure when one of the sides has zero
Lebesgue measure. And yet they do not coincide, as the first one gives zero mass to the diagonal,
and the second one gives mass one.
-/
/-- A measure on a product space equals the product measure of sigma-finite measures if they are
equal on rectangles. -/
theorem productBySections_eq {μ : Measure α} [SigmaFinite μ] {ν : Measure β} [SigmaFinite ν]
    {μν : Measure (α × β)}
    (h : ∀ s t, MeasurableSet s → MeasurableSet t → μν (s ×ˢ t) = μ s * ν t) :
    μ.productBySections ν = μν :=
  productBySections_eq_generateFrom (SigmaAlgebra.generateFrom_self _)
    (SigmaAlgebra.generateFrom_self _)
    (SigmaAlgebra.isPiSystem _) (SigmaAlgebra.isPiSystem _) μ.toFiniteSpanningSetsIn
    ν.toFiniteSpanningSetsIn fun s hs t ht => h s t hs ht

-- This is not true for σ-finite measures. See the discussion at
-- https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Uniqueness.20of.20sigma-finite.20measures.20on.20a.20product.20space/with/541741071
/-- Two finite measures on a product that are equal on products of sets are equal. -/
lemma ext_prod {α β : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β}
    {μ ν : Measure (α × β)} [IsFiniteMeasure μ]
    (h : ∀ {s : Set α} {t : Set β}, MeasurableSet s → MeasurableSet t → μ (s ×ˢ t) = ν (s ×ˢ t)) :
    μ = ν := by
  ext s hs
  have h_univ : μ univ = ν univ := by
    rw [← univ_prod_univ]
    exact h .univ .univ
  have : IsFiniteMeasure ν := ⟨by simp [← h_univ]⟩
  refine SigmaAlgebra.induction_on_inter generateFrom_prod.symm isPiSystem_prod (by simp)
    ?_ ?_ ?_ s hs
  · rintro - ⟨s, hs, t, ht, rfl⟩
    exact h hs ht
  · intro t ht h
    simp_rw [measure_compl ht (measure_ne_top _ _), h, h_univ]
  · intro f h_disj hf h_eq
    simp_rw [measure_iUnion h_disj hf, h_eq]

/-- Two finite measures on a product are equal iff they are equal on products of sets. -/
lemma ext_prod_iff {α β : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β}
    {μ ν : Measure (α × β)} [IsFiniteMeasure μ] :
    μ = ν
      ↔ ∀ {s : Set α} {t : Set β}, MeasurableSet s → MeasurableSet t → μ (s ×ˢ t) = ν (s ×ˢ t) :=
  ⟨fun h s t hs ht ↦ by rw [h], Measure.ext_prod⟩

/-- Two finite measures on a product `α × β × γ` that are equal on products of sets are equal.
See `ext_prod₃'` for the same statement for `(α × β) × γ`. -/
lemma ext_prod₃ {α β γ : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β}
    {mγ : SigmaAlgebra γ} {μ ν : Measure (α × β × γ)} [IsFiniteMeasure μ]
    (h : ∀ {s : Set α} {t : Set β} {u : Set γ},
      MeasurableSet s → MeasurableSet t → MeasurableSet u → μ (s ×ˢ t ×ˢ u) = ν (s ×ˢ t ×ˢ u)) :
    μ = ν := by
  ext s hs
  have h_univ : μ univ = ν univ := by
    simp_rw [← univ_prod_univ]
    exact h .univ .univ .univ
  have : IsFiniteMeasure ν := ⟨by simp [← h_univ]⟩
  let C₂ := image2 (· ×ˢ ·) { t : Set β | MeasurableSet t } { u : Set γ | MeasurableSet u }
  let C := image2 (· ×ˢ ·) { s : Set α | MeasurableSet s } C₂
  refine SigmaAlgebra.induction_on_inter (s := C) ?_ ?_ (by simp) ?_ ?_ ?_ s hs
  · refine (generateFrom_eq_prod (C := { s : Set α | MeasurableSet s }) (D := C₂) ?_
      generateFrom_prod isCountablySpanning_measurableSet ?_).symm
    · change generateFrom ((inferInstance : SigmaAlgebra α) : Set (Set α)) = _
      exact SigmaAlgebra.generateFrom_self _
    exact isCountablySpanning_measurableSet.prod isCountablySpanning_measurableSet
  · exact (SigmaAlgebra.isPiSystem _).prod isPiSystem_prod
  · rintro - ⟨s, hs, -, ⟨t, ht, u, hu, rfl⟩, rfl⟩
    exact h hs ht hu
  · intro t ht h
    simp_rw [measure_compl ht (measure_ne_top _ _), h, h_univ]
  · intro f h_disj hf h_eq
    simp_rw [measure_iUnion h_disj hf, h_eq]

/-- Two finite measures on a product `α × β × γ` are equal iff they are equal on products of sets.
See `ext_prod₃_iff'` for the same statement for `(α × β) × γ`. -/
lemma ext_prod₃_iff {α β γ : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β}
    {mγ : SigmaAlgebra γ} {μ ν : Measure (α × β × γ)} [IsFiniteMeasure μ] :
    μ = ν ↔ (∀ {s : Set α} {t : Set β} {u : Set γ},
      MeasurableSet s → MeasurableSet t → MeasurableSet u → μ (s ×ˢ t ×ˢ u) = ν (s ×ˢ t ×ˢ u)) :=
  ⟨fun h s t u hs ht hu ↦ by rw [h], Measure.ext_prod₃⟩

/-- Two finite measures on a product `(α × β) × γ` are equal iff they are equal on products of sets.
See `ext_prod₃_iff` for the same statement for `α × β × γ`. -/
lemma ext_prod₃_iff' {α β γ : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β}
    {mγ : SigmaAlgebra γ} {μ ν : Measure ((α × β) × γ)} [IsFiniteMeasure μ] :
    μ = ν ↔ (∀ {s : Set α} {t : Set β} {u : Set γ},
      MeasurableSet s → MeasurableSet t → MeasurableSet u →
      μ ((s ×ˢ t) ×ˢ u) = ν ((s ×ˢ t) ×ˢ u)) := by
  rw [← MeasurableEquiv.prodAssoc.map_measurableEquiv_injective.eq_iff, ext_prod₃_iff]
  have h_eq (ν : Measure ((α × β) × γ)) {s : Set α} {t : Set β} {u : Set γ}
      (hs : MeasurableSet s) (ht : MeasurableSet t) (hu : MeasurableSet u) :
      (ν.map MeasurableEquiv.prodAssoc
        MeasurableEquiv.prodAssoc.measurable.aemeasurable) (s ×ˢ (t ×ˢ u)) =
        ν ((s ×ˢ t) ×ˢ u) := by
    rw [map_apply (hs.prod (ht.prod hu))]
    congr 1 with x
    simp [MeasurableEquiv.prodAssoc]
  refine ⟨fun h s t u hs ht hu ↦ ?_, fun h s t u hs ht hu ↦ ?_⟩ <;> specialize h hs ht hu
  · rwa [h_eq μ hs ht hu, h_eq ν hs ht hu] at h
  · rwa [h_eq μ hs ht hu, h_eq ν hs ht hu]

/-- Two finite measures on a product `(α × β) × γ` that are equal on products of sets are equal.
See `ext_prod₃` for the same statement for `α × β × γ`. -/
alias ⟨_, ext_prod₃'⟩ := ext_prod₃_iff'

variable [SFinite μ]

theorem productBySections_swap :
    map Prod.swap (μ.productBySections ν) measurable_swap.aemeasurable = ν.productBySections μ := by
  have : sum (fun (i : ℕ × ℕ) ↦
      map Prod.swap ((sfiniteSeq μ i.1).productBySections (sfiniteSeq ν i.2))
        measurable_swap.aemeasurable) =
      sum (fun (i : ℕ × ℕ) ↦
        map Prod.swap ((sfiniteSeq μ i.2).productBySections (sfiniteSeq ν i.1))
          measurable_swap.aemeasurable) := by
    ext s hs
    rw [sum_apply _ hs, sum_apply _ hs]
    exact ((Equiv.prodComm ℕ ℕ).tsum_eq _).symm
  have hsum :
      map Prod.swap ((sum (sfiniteSeq μ)).productBySections (sum (sfiniteSeq ν)))
          measurable_swap.aemeasurable =
        (sum (sfiniteSeq ν)).productBySections (sum (sfiniteSeq μ)) := by
    rw [productBySections_sum, productBySections_sum, map_sum measurable_swap.aemeasurable, this]
    congr 1
    ext1 i
    refine (productBySections_eq ?_).symm
    intro s t hs ht
    simp_rw [map_apply (hs.prod ht) measurable_swap.aemeasurable, preimage_swap_prod,
      productBySections_prod, mul_comm]
  simpa only [sum_sfiniteSeq] using hsum

theorem measurePreserving_swap_productBySections :
    MeasurePreserving Prod.swap (μ.productBySections ν) (ν.productBySections μ) :=
  ⟨measurable_swap, productBySections_swap⟩

theorem productBySections_apply_symm {s : Set (α × β)} (hs : MeasurableSet s) :
    (μ.productBySections ν) s = ∫⁻ y, μ ((fun x => (x, y)) ⁻¹' s) ∂ν := by
  rw [← productBySections_swap, map_apply hs measurable_swap.aemeasurable,
    productBySections_apply (measurable_swap hs)]
  rfl

theorem ae_ae_comm {p : α → β → Prop} (h : MeasurableSet {x : α × β | p x.1 x.2}) :
    (∀ᵐ x ∂μ, ∀ᵐ y ∂ν, p x y) ↔ ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, p x y := calc
  _ ↔ ∀ᵐ x ∂μ.productBySections ν, p x.1 x.2 := .symm <| ae_prod_iff_ae_ae h
  _ ↔ ∀ᵐ x ∂ν.productBySections μ, p x.2 x.1 := by
    rw [← productBySections_swap, ae_map_iff (by fun_prop) h]; simp
  _ ↔ ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, p x y := ae_prod_iff_ae_ae <| measurable_swap h

/-- If `s ×ˢ t` is a null measurable set and `ν t ≠ 0`, then `s` is a null measurable set. -/
lemma _root_.MeasureTheory.NullMeasurableSet.left_of_prod {s : Set α} {t : Set β}
    (h : NullMeasurableSet (s ×ˢ t) (μ.productBySections ν)) (ht : ν t ≠ 0) :
    NullMeasurableSet s μ := by
  refine .right_of_prod ?_ ht
  rw [← preimage_swap_prod]
  exact h.preimage measurePreserving_swap_productBySections.quasiMeasurePreserving

/-- If `Prod.fst ⁻¹' s` is a null measurable set and `ν ≠ 0`, then `s` is a null measurable set. -/
lemma _root_.MeasureTheory.NullMeasurableSet.of_preimage_fst [NeZero ν] {s : Set α}
    (h : NullMeasurableSet (Prod.fst ⁻¹' s) (μ.productBySections ν)) : NullMeasurableSet s μ :=
  .left_of_prod (by rwa [prod_univ]) (NeZero.ne (ν univ))

/-- `Prod.fst ⁻¹' s` is null measurable w.r.t. `μ.productBySections ν` iff `s` is null measurable
w.r.t. `μ`
provided that `ν ≠ 0`. -/
lemma nullMeasurableSet_preimage_fst [NeZero ν] {s : Set α} :
    NullMeasurableSet (Prod.fst ⁻¹' s) (μ.productBySections ν) ↔ NullMeasurableSet s μ :=
  ⟨.of_preimage_fst, (.preimage · quasiMeasurePreserving_fst)⟩

lemma nullMeasurable_comp_fst [NeZero ν] {f : α → γ} :
    NullMeasurable (f ∘ Prod.fst) (μ.productBySections ν) ↔ NullMeasurable f μ :=
  forall₂_congr fun s _ ↦ nullMeasurableSet_preimage_fst (s := f ⁻¹' s)

/-- The product of two non-null sets is null measurable
if and only if both of them are null measurable. -/
lemma nullMeasurableSet_prod_of_ne_zero {s : Set α} {t : Set β} (hs : μ s ≠ 0) (ht : ν t ≠ 0) :
    NullMeasurableSet (s ×ˢ t) (μ.productBySections ν) ↔
      NullMeasurableSet s μ ∧ NullMeasurableSet t ν :=
  ⟨fun h ↦ ⟨h.left_of_prod ht, h.right_of_prod hs⟩, fun ⟨hs, ht⟩ ↦ hs.prod ht⟩

/-- The product of two sets is null measurable
if and only if both of them are null measurable or one of them has measure zero. -/
lemma nullMeasurableSet_prod {s : Set α} {t : Set β} :
    NullMeasurableSet (s ×ˢ t) (μ.productBySections ν) ↔
      NullMeasurableSet s μ ∧ NullMeasurableSet t ν ∨ μ s = 0 ∨ ν t = 0 := by
  rcases eq_or_ne (μ s) 0 with hs | hs; · simp [NullMeasurableSet.of_null, *]
  rcases eq_or_ne (ν t) 0 with ht | ht; · simp [NullMeasurableSet.of_null, *]
  simp [*, nullMeasurableSet_prod_of_ne_zero]

theorem prodAssoc_productBySections [SFinite τ] :
    map MeasurableEquiv.prodAssoc ((μ.productBySections ν).productBySections τ)
      MeasurableEquiv.prodAssoc.measurable.aemeasurable =
        μ.productBySections (ν.productBySections τ) := by
  have : sum (fun (p : ℕ × ℕ × ℕ) ↦
        (sfiniteSeq μ p.1).productBySections
          ((sfiniteSeq ν p.2.1).productBySections (sfiniteSeq τ p.2.2)))
      = sum (fun (p : (ℕ × ℕ) × ℕ) ↦
        (sfiniteSeq μ p.1.1).productBySections
          ((sfiniteSeq ν p.1.2).productBySections (sfiniteSeq τ p.2))) := by
    ext s hs
    rw [sum_apply _ hs, sum_apply _ hs, ← (Equiv.prodAssoc _ _ _).tsum_eq]
    simp only [Equiv.prodAssoc_apply]
  have hsum :
      map MeasurableEquiv.prodAssoc
          (((sum (sfiniteSeq μ)).productBySections (sum (sfiniteSeq ν))).productBySections
            (sum (sfiniteSeq τ)))
          MeasurableEquiv.prodAssoc.measurable.aemeasurable =
        (sum (sfiniteSeq μ)).productBySections
          ((sum (sfiniteSeq ν)).productBySections (sum (sfiniteSeq τ))) := by
    simp only [productBySections_sum, map_sum MeasurableEquiv.prodAssoc.measurable.aemeasurable,
      this]
    congr
    ext1 i
    refine (productBySections_eq_generateFrom (SigmaAlgebra.generateFrom_self _) generateFrom_prod
      (SigmaAlgebra.isPiSystem _) isPiSystem_prod ((sfiniteSeq μ i.1.1)).toFiniteSpanningSetsIn
      ((sfiniteSeq ν i.1.2).toFiniteSpanningSetsIn.prod (sfiniteSeq τ i.2).toFiniteSpanningSetsIn)
        ?_).symm
    rintro s hs _ ⟨t, ht, u, hu, rfl⟩
    simp_rw [map_apply (MeasurableSet.prod hs (MeasurableSet.prod ht hu))
        MeasurableEquiv.prodAssoc.measurable.aemeasurable,
      MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, Equiv.prod_assoc_preimage,
      productBySections_prod, mul_assoc]
  simpa only [sum_sfiniteSeq] using hsum

/-! ### The product of specific measures -/

theorem productBySections_restrict (s : Set α) (t : Set β) :
    (μ.restrict s).productBySections (ν.restrict t) =
      (μ.productBySections ν).restrict (s ×ˢ t) := by
  have hsum :
      ((sum (sfiniteSeq μ)).restrict s).productBySections ((sum (sfiniteSeq ν)).restrict t) =
        ((sum (sfiniteSeq μ)).productBySections (sum (sfiniteSeq ν))).restrict (s ×ˢ t) := by
    simp only [restrict_sum_of_countable, productBySections_sum]
    congr 1
    ext1 i
    refine productBySections_eq fun s' t' hs' ht' => ?_
    rw [restrict_apply (hs'.prod ht'), prod_inter_prod, productBySections_prod, restrict_apply hs',
      restrict_apply ht']
  simpa only [sum_sfiniteSeq] using hsum

theorem restrict_productBySections_eq_productBySections_univ (s : Set α) :
    (μ.restrict s).productBySections ν = (μ.productBySections ν).restrict (s ×ˢ univ) := by
  simpa only [restrict_univ] using productBySections_restrict (μ := μ) (ν := ν) s univ

theorem productBySections_dirac (y : β) :
    μ.productBySections (dirac y) =
      map (fun x => (x, y)) μ measurable_prodMk_right.aemeasurable := by
  classical
  rw [← sum_sfiniteSeq μ, productBySections_sum_left, map_sum measurable_prodMk_right.aemeasurable]
  congr
  ext1 i
  refine productBySections_eq fun s t hs ht => ?_
  simp_rw [map_apply (hs.prod ht) measurable_prodMk_right.aemeasurable,
    mk_preimage_prod_left_eq_if, measure_if,
    dirac_apply' _ ht, ← indicator_mul_right _ fun _ => sfiniteSeq μ i s, Pi.one_apply, mul_one]

theorem dirac_productBySections (x : α) :
    (dirac x).productBySections ν = map (Prod.mk x) ν measurable_prodMk_left.aemeasurable := by
  classical
  have hsum :
      (dirac x).productBySections (sum (sfiniteSeq ν)) =
        map (Prod.mk x) (sum (sfiniteSeq ν)) measurable_prodMk_left.aemeasurable := by
    rw [productBySections_sum_right, map_sum measurable_prodMk_left.aemeasurable]
    congr
    ext1 i
    refine productBySections_eq fun s t hs ht => ?_
    simp_rw [map_apply (hs.prod ht) measurable_prodMk_left.aemeasurable,
      mk_preimage_prod_right_eq_if, measure_if,
      dirac_apply' _ hs, ← indicator_mul_left _ _ fun _ => sfiniteSeq ν i t, Pi.one_apply, one_mul]
  simpa only [sum_sfiniteSeq] using hsum

theorem dirac_productBySections_dirac {x : α} {y : β} :
    (dirac x).productBySections (dirac y) = dirac (x, y) := by
  rw [productBySections_dirac, map_dirac' measurable_prodMk_right]

theorem productBySections_add (ν' : Measure β) [SFinite ν'] :
    μ.productBySections (ν + ν') = μ.productBySections ν + μ.productBySections ν' := by
  simp_rw [← sum_sfiniteSeq ν, ← sum_sfiniteSeq ν', sum_add_sum, ← sum_sfiniteSeq μ,
    productBySections_sum,
    sum_add_sum]
  congr
  ext1 i
  refine productBySections_eq fun s t _ _ => ?_
  simp_rw [add_apply, productBySections_prod, left_distrib]

theorem add_productBySections (μ' : Measure α) [SFinite μ'] :
    (μ + μ').productBySections ν = μ.productBySections ν + μ'.productBySections ν := by
  simp_rw [← sum_sfiniteSeq μ, ← sum_sfiniteSeq μ', sum_add_sum, ← sum_sfiniteSeq ν,
    productBySections_sum,
    sum_add_sum]
  congr
  ext1 i
  refine productBySections_eq fun s t _ _ => ?_
  simp_rw [add_apply, productBySections_prod, right_distrib]

theorem map_productBySections_map {δ} [SigmaAlgebra δ] {f : α → β} {g : γ → δ} (μa : Measure α)
    (μc : Measure γ) [SFinite μa] [SFinite μc] (hf : Measurable f) (hg : Measurable g) :
    (map f μa hf.aemeasurable).productBySections (map g μc hg.aemeasurable) =
      map (Prod.map f g) (μa.productBySections μc) (hf.prodMap hg).aemeasurable := by
  simp_rw [← sum_sfiniteSeq μa, ← sum_sfiniteSeq μc, map_sum hf.aemeasurable,
    map_sum hg.aemeasurable, productBySections_sum, map_sum (hf.prodMap hg).aemeasurable]
  congr
  ext1 i
  refine productBySections_eq fun s t hs ht => ?_
  rw [map_apply (hs.prod ht) (hf.prodMap hg).aemeasurable,
    map_apply hs hf.aemeasurable, map_apply ht hg.aemeasurable]
  exact productBySections_prod (f ⁻¹' s) (g ⁻¹' t)

-- `productBySections_smul_right` needs an instance to get `SFinite (c • ν)` from `SFinite ν`,
-- hence it is placed in the `WithDensity` file, where the instance is defined.
lemma productBySections_smul_left {μ : Measure α} {R : Type*} [SMul R ℝ≥0∞]
    [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (c : R) : (c • μ).productBySections ν = c • (μ.productBySections ν) := by
  ext s hs
  rw [productBySections_apply hs, Measure.smul_apply, productBySections_apply hs]
  simp

end Measure

namespace MeasurePreserving

variable {δ : Type*} [SigmaAlgebra δ] {μa : Measure α} {μb : Measure β} {μc : Measure γ}
  {μd : Measure δ}

lemma aemeasurable_prodMk_of_skew [SFinite μa] [SFinite μc]
    {f : α → β} (hf : MeasurePreserving f μa μb) {g : α → γ → δ}
    (hgm : Measurable (uncurry g))
    (hg : ∀ᵐ a ∂μa, map (g a) μc hgm.of_uncurry_left.aemeasurable = μd) :
    AEMeasurable
      (fun b : β => map (Prod.mk b) μd measurable_prodMk_left.aemeasurable) μb := by
  rcases eq_or_ne μa 0 with hμa | hμa
  · have hμb : μb = 0 := by
      calc
        μb = μa.map f hf.aemeasurable := hf.map_eq.symm
        _ = 0 := (Measure.map_eq_zero_iff hf.aemeasurable).2 hμa
    rw [hμb]
    fun_prop
  · let _ : NeZero μa := ⟨hμa⟩
    let _ : SFinite μd := by
      obtain ⟨a, ha⟩ : ∃ a, map (g a) μc hgm.of_uncurry_left.aemeasurable = μd := hg.exists
      rw [← ha]
      infer_instance
    exact Measurable.map_prodMk_left.aemeasurable

/-- Let `f : α → β` be a measure-preserving map.
For a.e. all `a`, let `g a : γ → δ` be a measure-preserving map.
Also suppose that `g` is measurable as a function of two arguments.
Then the map `fun (a, c) ↦ (f a, g a c)` is a measure-preserving map
for the product measures on `α × γ` and `β × δ`.

Some authors call a map of the form `fun (a, c) ↦ (f a, g a c)` a *skew product* over `f`,
thus the choice of a name.
-/
theorem skew_product [SFinite μa] [SFinite μc] {f : α → β} (hf : MeasurePreserving f μa μb)
    {g : α → γ → δ} (hgm : Measurable (uncurry g))
    (hg : ∀ᵐ a ∂μa, map (g a) μc hgm.of_uncurry_left.aemeasurable = μd) :
    MeasurePreserving (fun p : α × γ => (f p.1, g p.1 p.2)) (μa.productBySections μc)
      (μb.productBySections μd (HasAEMeasurableSectionMeasures.of_aemeasurable
        (aemeasurable_prodMk_of_skew hf hgm hg))) := by
  have : Measurable fun p : α × γ => (f p.1, g p.1 p.2) := (hf.1.comp measurable_fst).prodMk hgm
  use this
  /- if `μa = 0`, then the lemma is trivial, otherwise we can use `hg`
    to deduce `SFinite μd`. -/
  rcases eq_zero_or_neZero μa with rfl | _
  · simp [← hf.map_eq]
  let _ : SFinite μd := by
    obtain ⟨a, ha⟩ : ∃ a, map (g a) μc hgm.of_uncurry_left.aemeasurable = μd := hg.exists
    rw [← ha]
    infer_instance
  -- Thus we can use the integral formula for the product measure, and compute things explicitly
  ext s hs
  rw [map_apply hs this.aemeasurable, Measure.productBySections_apply (this hs),
    Measure.productBySections_apply hs (HasAEMeasurableSectionMeasures.of_aemeasurable
      (aemeasurable_prodMk_of_skew hf hgm hg)),
    ← hf.lintegral_comp (measurable_measure_prodMk_left hs)]
  apply lintegral_congr_ae
  filter_upwards [hg] with a ha
  rw [← ha, map_apply (measurable_prodMk_left hs) hgm.of_uncurry_left.aemeasurable,
    preimage_preimage,
    preimage_preimage]

/-- If `f : α → β` sends the measure `μa` to `μb` and `g : γ → δ` sends the measure `μc` to `μd`,
then `Prod.map f g` sends `μa.productBySections μc` to `μb.productBySections μd`. -/
protected theorem prod [SFinite μa] [SFinite μc] {f : α → β} {g : γ → δ}
    (hf : MeasurePreserving f μa μb) (hg : MeasurePreserving g μc μd) :
    MeasurePreserving (Prod.map f g) (μa.productBySections μc)
      (μb.productBySections μd
        (HasAEMeasurableSectionMeasures.of_aemeasurable (aemeasurable_prodMk_of_skew hf
        (show Measurable (uncurry fun _ : α => g) from hg.1.comp measurable_snd)
        (ae_of_all _ fun _ => hg.map_eq)))) :=
  have : Measurable (uncurry fun _ : α => g) := hg.1.comp measurable_snd
  hf.skew_product this <| ae_of_all _ fun _ => hg.map_eq

end MeasurePreserving

namespace QuasiMeasurePreserving

theorem prod_of_right {f : α × β → γ} {μ : Measure α} {ν : Measure β} {τ : Measure γ}
    (hf : Measurable f) [SFinite ν]
    (h2f : ∀ᵐ x ∂μ, QuasiMeasurePreserving (fun y => f (x, y)) ν τ) :
    QuasiMeasurePreserving f (μ.productBySections ν) τ := by
  refine ⟨hf, ?_⟩
  refine AbsolutelyContinuous.mk fun s hs h2s => ?_
  rw [map_apply hs hf.aemeasurable, Measure.productBySections_apply (hf hs)];
  simp_rw [preimage_preimage]
  rw [lintegral_congr_ae (h2f.mono fun x hx => hx.preimage_null h2s), lintegral_zero]

theorem prod_of_left {α β γ} [SigmaAlgebra α] [SigmaAlgebra β] [SigmaAlgebra γ]
    {f : α × β → γ} {μ : Measure α} {ν : Measure β} {τ : Measure γ} (hf : Measurable f)
    [SFinite μ] [SFinite ν]
    (h2f : ∀ᵐ y ∂ν, QuasiMeasurePreserving (fun x => f (x, y)) μ τ) :
    QuasiMeasurePreserving f (μ.productBySections ν) τ := by
  rw [← productBySections_swap]
  convert!
    (QuasiMeasurePreserving.prod_of_right (hf.comp measurable_swap) h2f).comp
      ((measurable_swap.measurePreserving
        (ν.productBySections μ (hasAEMeasurableSectionMeasures_of_sfinite ν μ))).symm
          MeasurableEquiv.prodComm).quasiMeasurePreserving

@[fun_prop]
protected theorem fst [SFinite τ] {f : α → β × γ}
    (hf : QuasiMeasurePreserving f μ (ν.productBySections τ)) :
    QuasiMeasurePreserving (fun x ↦ (f x).1) μ ν :=
  (quasiMeasurePreserving_fst (μ := ν) (ν := τ)).comp hf

@[fun_prop]
protected theorem snd [SFinite τ] {f : α → β × γ}
    (hf : QuasiMeasurePreserving f μ (ν.productBySections τ)) :
    QuasiMeasurePreserving (fun x ↦ (f x).2) μ τ :=
  (quasiMeasurePreserving_snd (μ := ν) (ν := τ)).comp hf

@[fun_prop]
protected theorem prodMap {ω : Type*} {mω : SigmaAlgebra ω} {υ : Measure ω}
    [SFinite μ] [SFinite τ] [SFinite υ] {f : α → β} {g : γ → ω}
    (hf : QuasiMeasurePreserving f μ ν) (hg : QuasiMeasurePreserving g τ υ) :
    QuasiMeasurePreserving (Prod.map f g) (μ.productBySections τ) (ν.productBySections υ) := by
  refine ⟨by fun_prop, ?_⟩
  rw [← map_productBySections_map _ _ (by fun_prop) (by fun_prop)]
  exact hf.absolutelyContinuous.prod hg.absolutelyContinuous

end QuasiMeasurePreserving

end MeasureTheory

open MeasureTheory.Measure

section

theorem AEMeasurable.prod_swap [SFinite μ] [SFinite ν] {f : β × α → γ}
    (hf : AEMeasurable f (ν.productBySections μ)) :
    AEMeasurable (fun z : α × β => f z.swap) (μ.productBySections ν) := by
  rw [← Measure.productBySections_swap] at hf
  exact hf.comp_measurable measurable_swap

theorem MeasureTheory.NullMeasurable.comp_fst [SFinite ν] {f : α → γ} (hf : NullMeasurable f μ) :
    NullMeasurable (fun z : α × β => f z.1) (μ.productBySections ν) :=
  hf.comp_quasiMeasurePreserving quasiMeasurePreserving_fst

theorem AEMeasurable.comp_fst [SFinite ν] {f : α → γ} (hf : AEMeasurable f μ) :
    AEMeasurable (fun z : α × β => f z.1) (μ.productBySections ν) :=
  hf.comp_quasiMeasurePreserving quasiMeasurePreserving_fst

theorem MeasureTheory.NullMeasurable.comp_snd [SFinite ν] {f : β → γ} (hf : NullMeasurable f ν) :
    NullMeasurable (fun z : α × β => f z.2) (μ.productBySections ν) :=
  hf.comp_quasiMeasurePreserving quasiMeasurePreserving_snd

theorem AEMeasurable.comp_snd [SFinite ν] {f : β → γ} (hf : AEMeasurable f ν) :
    AEMeasurable (fun z : α × β => f z.2) (μ.productBySections ν) :=
  hf.comp_quasiMeasurePreserving quasiMeasurePreserving_snd

theorem AEMeasurable.lintegral_prod_right' [SFinite ν] {f : α × β → ℝ≥0∞}
    (hf : AEMeasurable f (μ.productBySections ν)) : AEMeasurable (fun x ↦ ∫⁻ y, f (x, y) ∂ν) μ := by
  obtain ⟨g, hg, hfg⟩ := hf
  refine ⟨fun x ↦ ∫⁻ y, g (x, y) ∂ν, by fun_prop, ?_⟩
  exact (ae_ae_of_ae_prod hfg).mono fun x hfg' ↦ lintegral_congr_ae hfg'

@[fun_prop]
theorem AEMeasurable.lintegral_prod_right [SFinite ν] {f : α → β → ℝ≥0∞}
    (hf : AEMeasurable f.uncurry (μ.productBySections ν)) :
    AEMeasurable (fun x ↦ ∫⁻ y, f x y ∂ν) μ :=
  hf.lintegral_prod_right'

theorem AEMeasurable.lintegral_prod_left' [SFinite ν] [SFinite μ] {f : α × β → ℝ≥0∞}
    (hf : AEMeasurable f (μ.productBySections ν)) : AEMeasurable (fun y ↦ ∫⁻ x, f (x, y) ∂μ) ν :=
  hf.prod_swap.lintegral_prod_right'

@[fun_prop]
theorem AEMeasurable.lintegral_prod_left [SFinite ν] [SFinite μ] {f : α → β → ℝ≥0∞}
    (hf : AEMeasurable f.uncurry (μ.productBySections ν)) :
    AEMeasurable (fun y ↦ ∫⁻ x, f x y ∂μ) ν :=
  hf.lintegral_prod_left'

end

namespace MeasureTheory

/-! ### The Lebesgue integral on a product -/

variable [SFinite ν]

theorem lintegral_productBySections_swap [SFinite μ] (f : α × β → ℝ≥0∞) :
    ∫⁻ z, f z.swap ∂ν.productBySections μ = ∫⁻ z, f z ∂μ.productBySections ν :=
  measurePreserving_swap_productBySections.lintegral_comp_emb
    MeasurableEquiv.prodComm.measurableEmbedding f

/-- **Tonelli's Theorem**: For `ℝ≥0∞`-valued almost everywhere measurable functions on `α × β`,
  the integral of `f` is equal to the iterated integral. -/
theorem lintegral_productBySections (f : α × β → ℝ≥0∞)
    (hf : AEMeasurable f (μ.productBySections ν)) :
    ∫⁻ z, f z ∂μ.productBySections ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  rw [Measure.productBySections_eq_bind Measurable.map_prodMk_left.aemeasurable] at *
  rw [lintegral_bind Measurable.map_prodMk_left.aemeasurable hf]
  apply lintegral_congr_ae
  filter_upwards [Measurable.map_prodMk_left.aemeasurable.ae_of_bind hf] with a ha
  exact lintegral_map' (by fun_prop) ha

theorem lintegral_productBySections_le (f : α × β → ℝ≥0∞) :
    ∫⁻ z, f z ∂μ.productBySections ν ≤ ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  rw [Measure.productBySections_eq_bind Measurable.map_prodMk_left.aemeasurable]
  exact (lintegral_bind_le _ _ Measurable.map_prodMk_left.aemeasurable).trans <|
    lintegral_mono fun a ↦ lintegral_map_le _ (by fun_prop)

/-- **Tonelli's Theorem for set integrals**: For `ℝ≥0∞`-valued almost everywhere measurable
functions on `s ×ˢ t`, the integral of `f` on `s ×ˢ t` is equal to the iterated integral on `s`
and `t` respectively. -/
theorem setLIntegral_productBySections [SFinite μ] {s : Set α} {t : Set β} (f : α × β → ℝ≥0∞)
    (hf : AEMeasurable f ((μ.productBySections ν).restrict (s ×ˢ t))) :
    ∫⁻ z in s ×ˢ t, f z ∂μ.productBySections ν = ∫⁻ x in s, ∫⁻ y in t, f (x, y) ∂ν ∂μ := by
  rw [← Measure.productBySections_restrict,
    lintegral_productBySections _ (by rwa [Measure.productBySections_restrict])]

/-- The symmetric version of Tonelli's Theorem: For `ℝ≥0∞`-valued almost everywhere measurable
functions on `α × β`, the integral of `f` is equal to the iterated integral, in reverse order. -/
theorem lintegral_productBySections_symm [SFinite μ] (f : α × β → ℝ≥0∞)
    (hf : AEMeasurable f (μ.productBySections ν)) :
    ∫⁻ z, f z ∂μ.productBySections ν = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν := by
  simp_rw [← lintegral_productBySections_swap f]
  exact lintegral_productBySections _ hf.prod_swap

/-- The symmetric version of Tonelli's Theorem: For `ℝ≥0∞`-valued measurable
functions on `α × β`, the integral of `f` is equal to the iterated integral, in reverse order. -/
theorem lintegral_productBySections_symm' [SFinite μ] (f : α × β → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂μ.productBySections ν = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν :=
  lintegral_productBySections_symm f hf.aemeasurable

/-- The symmetric version of Tonelli's Theorem for set integrals: For `ℝ≥0∞`-valued almost
everywhere measurable functions on `s ×ˢ t`, the integral of `f` on `s ×ˢ t` is equal to the
iterated integral on `t` and `s` respectively. -/
theorem setLIntegral_productBySections_symm [SFinite μ] {s : Set α} {t : Set β} (f : α × β → ℝ≥0∞)
    (hf : AEMeasurable f ((μ.productBySections ν).restrict (s ×ˢ t))) :
    ∫⁻ z in s ×ˢ t, f z ∂μ.productBySections ν = ∫⁻ y in t, ∫⁻ x in s, f (x, y) ∂μ ∂ν := by
  rw [← Measure.productBySections_restrict, ← lintegral_productBySections_swap,
    Measure.productBySections_restrict,
    setLIntegral_productBySections]
  · rfl
  · refine AEMeasurable.comp_measurable measurable_swap ?_
    have hmeasure :
        map Prod.swap ((ν.productBySections μ).restrict (t ×ˢ s)) measurable_swap.aemeasurable =
          (μ.productBySections ν).restrict (s ×ˢ t) := by
      calc
        map Prod.swap ((ν.productBySections μ).restrict (t ×ˢ s)) measurable_swap.aemeasurable =
            map Prod.swap ((ν.restrict t).productBySections (μ.restrict s))
              measurable_swap.aemeasurable := by
          congr 1
          exact (productBySections_restrict (μ := ν) (ν := μ) t s).symm
        _ = (μ.restrict s).productBySections (ν.restrict t) := productBySections_swap
        _ = (μ.productBySections ν).restrict (s ×ˢ t) := productBySections_restrict s t
    exact hmeasure.symm ▸ hf

/-- The reversed version of **Tonelli's Theorem**. In this version `f` is in curried form, which
makes it easier for the elaborator to figure out `f` automatically. -/
theorem lintegral_lintegral ⦃f : α → β → ℝ≥0∞⦄
    (hf : AEMeasurable (uncurry f) (μ.productBySections ν)) :
    ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ z, f z.1 z.2 ∂μ.productBySections ν :=
  (lintegral_productBySections _ hf).symm

/-- The reversed version of **Tonelli's Theorem** (symmetric version). In this version `f` is in
curried form, which makes it easier for the elaborator to figure out `f` automatically. -/
theorem lintegral_lintegral_symm [SFinite μ] ⦃f : α → β → ℝ≥0∞⦄
    (hf : AEMeasurable (uncurry f) (μ.productBySections ν)) :
    ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ z, f z.2 z.1 ∂ν.productBySections μ :=
  (lintegral_productBySections_symm _ hf.prod_swap).symm

/-- Change the order of Lebesgue integration. -/
theorem lintegral_lintegral_swap [SFinite μ] ⦃f : α → β → ℝ≥0∞⦄
    (hf : AEMeasurable (uncurry f) (μ.productBySections ν)) :
    ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ y, ∫⁻ x, f x y ∂μ ∂ν :=
  (lintegral_lintegral hf).trans (lintegral_productBySections_symm _ hf)

theorem lintegral_productBySections_mul {f : α → ℝ≥0∞} {g : β → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g ν) :
    ∫⁻ z, f z.1 * g z.2 ∂μ.productBySections ν = (∫⁻ x, f x ∂μ) * ∫⁻ y, g y ∂ν := by
  rw [lintegral_productBySections _ (by fun_prop)]
  simp [lintegral_lintegral_mul hf hg]

lemma _root_.Measurable.measurable_bind_left {f : α → β → Measure γ} (hf : Measurable f.uncurry) :
    Measurable (fun a ↦ ν.bind (f a) hf.of_uncurry_left.aemeasurable) := by
  refine measurable_measure.2 fun s hs ↦ ?_
  simp_rw [ν.bind_apply hs hf.of_uncurry_left.aemeasurable]
  apply Measurable.lintegral_prod_left
  convert measurable_measure.1 (hf.comp measurable_swap) s hs
  grind

lemma _root_.Measurable.measurable_bind_right [SFinite μ] {f : α → β → Measure γ}
    (hf : Measurable f.uncurry) :
    Measurable (fun b ↦ μ.bind (f · b) hf.of_uncurry_right.aemeasurable) := by
  refine measurable_measure.2 fun s hs ↦ ?_
  simp_rw [bind_apply hs hf.of_uncurry_right.aemeasurable]
  apply Measurable.lintegral_prod_right
  convert measurable_measure.1 (hf.comp measurable_swap) s hs
  grind

theorem Measure.bind_comm [SFinite μ] {f : α → β → Measure γ} (hf : Measurable f.uncurry) :
    μ.bind (fun a ↦ ν.bind (f a) hf.of_uncurry_left.aemeasurable)
        hf.measurable_bind_left.aemeasurable =
      ν.bind (fun b ↦ μ.bind (f · b) hf.of_uncurry_right.aemeasurable)
        hf.measurable_bind_right.aemeasurable := by
  ext s hs
  simp_rw [bind_apply hs hf.measurable_bind_left.aemeasurable,
    bind_apply hs hf.of_uncurry_left.aemeasurable,
    bind_apply hs hf.measurable_bind_right.aemeasurable,
    bind_apply hs hf.of_uncurry_right.aemeasurable]
  rw [lintegral_lintegral_swap]
  exact (measurable_measure.1 hf s hs).aemeasurable

/-! ### Marginals of a measure defined on a product -/


namespace Measure

variable {ρ : Measure (α × β)}

/-- Marginal measure on `α` obtained from a measure `ρ` on `α × β`, defined by `ρ.map Prod.fst`. -/
noncomputable def fst (ρ : Measure (α × β)) : Measure α :=
  ρ.map Prod.fst measurable_fst.aemeasurable

theorem fst_apply {s : Set α} (hs : MeasurableSet s) : ρ.fst s = ρ (Prod.fst ⁻¹' s) := by
  rw [fst, Measure.map_apply hs measurable_fst.aemeasurable]

theorem fst_univ : ρ.fst univ = ρ univ := by rw [fst_apply MeasurableSet.univ, preimage_univ]

@[simp] theorem fst_zero : fst (0 : Measure (α × β)) = 0 := by simp [fst]

instance [SFinite ρ] : SFinite ρ.fst := by
  rw [fst]
  infer_instance

instance fst.instIsFiniteMeasure [IsFiniteMeasure ρ] : IsFiniteMeasure ρ.fst := by
  rw [fst]
  infer_instance

instance fst.instIsProbabilityMeasure [IsProbabilityMeasure ρ] : IsProbabilityMeasure ρ.fst where
  measure_univ := by
    rw [fst_univ]
    exact measure_univ

instance fst.instIsZeroOrProbabilityMeasure [IsZeroOrProbabilityMeasure ρ] :
    IsZeroOrProbabilityMeasure ρ.fst := by
  rcases eq_zero_or_isProbabilityMeasure ρ with h | h
  · simp only [h, fst_zero]
    infer_instance
  · infer_instance

@[simp]
lemma fst_productBySections [IsProbabilityMeasure ν] : (μ.productBySections ν).fst = μ := by
  ext1 s hs
  rw [fst_apply hs, ← prod_univ, productBySections_prod, measure_univ, mul_one]

theorem fst_map_prodMk₀ {X : α → β} {Y : α → γ} {μ : Measure α}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    (μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).fst = μ.map X hX := by
  ext1 s hs
  rw [Measure.fst_apply hs, Measure.map_apply (measurable_fst hs) (hX.prodMk hY),
    Measure.map_apply hs hX, ← prod_univ, mk_preimage_prod, preimage_univ,
    inter_univ]

theorem fst_map_prodMk {X : α → β} {Y : α → γ} {μ : Measure α} (hX : Measurable X)
    (hY : Measurable Y) :
    (μ.map (fun a => (X a, Y a)) (hX.prodMk hY).aemeasurable).fst =
      μ.map X hX.aemeasurable :=
  fst_map_prodMk₀ hX.aemeasurable hY.aemeasurable

@[simp]
lemma fst_add {μ ν : Measure (α × β)} : (μ + ν).fst = μ.fst + ν.fst :=
  Measure.map_add _ _ measurable_fst

lemma fst_sum {ι : Type*} (μ : ι → Measure (α × β)) : (sum μ).fst = sum (fun n ↦ (μ n).fst) :=
  Measure.map_sum measurable_fst.aemeasurable

@[gcongr]
theorem fst_mono {μ : Measure (α × β)} (h : ρ ≤ μ) : ρ.fst ≤ μ.fst := map_mono h measurable_fst

/-- Marginal measure on `β` obtained from a measure on `ρ` `α × β`, defined by `ρ.map Prod.snd`. -/
noncomputable def snd (ρ : Measure (α × β)) : Measure β :=
  ρ.map Prod.snd measurable_snd.aemeasurable

theorem snd_apply {s : Set β} (hs : MeasurableSet s) : ρ.snd s = ρ (Prod.snd ⁻¹' s) := by
  rw [snd, Measure.map_apply hs measurable_snd.aemeasurable]

theorem snd_univ : ρ.snd univ = ρ univ := by rw [snd_apply MeasurableSet.univ, preimage_univ]

@[simp] theorem snd_zero : snd (0 : Measure (α × β)) = 0 := by simp [snd]

instance [SFinite ρ] : SFinite ρ.snd := by
  rw [snd]
  infer_instance

instance snd.instIsFiniteMeasure [IsFiniteMeasure ρ] : IsFiniteMeasure ρ.snd := by
  rw [snd]
  infer_instance

instance snd.instIsProbabilityMeasure [IsProbabilityMeasure ρ] : IsProbabilityMeasure ρ.snd where
  measure_univ := by
    rw [snd_univ]
    exact measure_univ

instance snd.instIsZeroOrProbabilityMeasure [IsZeroOrProbabilityMeasure ρ] :
    IsZeroOrProbabilityMeasure ρ.snd := by
  rcases eq_zero_or_isProbabilityMeasure ρ with h | h
  · simp only [h, snd_zero]
    infer_instance
  · infer_instance

@[simp]
lemma snd_productBySections [IsProbabilityMeasure μ] : (μ.productBySections ν).snd = ν := by
  ext1 s hs
  rw [snd_apply hs, ← univ_prod, productBySections_prod, measure_univ, one_mul]

theorem snd_map_prodMk₀ {X : α → β} {Y : α → γ} {μ : Measure α} (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) :
    (μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).snd = μ.map Y hY := by
  ext1 s hs
  rw [Measure.snd_apply hs, Measure.map_apply (measurable_snd hs) (hX.prodMk hY),
    Measure.map_apply hs hY, ← univ_prod, mk_preimage_prod, preimage_univ,
    univ_inter]

theorem snd_map_prodMk {X : α → β} {Y : α → γ} {μ : Measure α} (hX : Measurable X)
    (hY : Measurable Y) :
    (μ.map (fun a => (X a, Y a)) (hX.prodMk hY).aemeasurable).snd =
      μ.map Y hY.aemeasurable :=
  snd_map_prodMk₀ hX.aemeasurable hY.aemeasurable

@[simp]
lemma snd_add {μ ν : Measure (α × β)} : (μ + ν).snd = μ.snd + ν.snd :=
  Measure.map_add _ _ measurable_snd

lemma snd_sum {ι : Type*} (μ : ι → Measure (α × β)) : (sum μ).snd = sum (fun n ↦ (μ n).snd) :=
  map_sum measurable_snd.aemeasurable

@[gcongr]
theorem snd_mono {μ : Measure (α × β)} (h : ρ ≤ μ) : ρ.snd ≤ μ.snd := map_mono h measurable_snd

@[simp] lemma fst_map_swap : (ρ.map Prod.swap measurable_swap.aemeasurable).fst = ρ.snd := by
  rw [Measure.fst, Measure.map_map measurable_swap.aemeasurable measurable_fst.aemeasurable]
  rfl

@[simp] lemma snd_map_swap : (ρ.map Prod.swap measurable_swap.aemeasurable).snd = ρ.fst := by
  rw [Measure.snd, Measure.map_map measurable_swap.aemeasurable measurable_snd.aemeasurable]
  rfl

end Measure

section MeasurePreserving

-- Note that these results cannot be put in the previous `measurePreserving` section since
-- they use `lintegral_productBySections`.

/-- The measurable equiv induced by the equiv `(α × β) × γ ≃ α × (β × γ)` is measure preserving. -/
theorem _root_.MeasureTheory.measurePreserving_prodAssoc (μa : Measure α) (μb : Measure β)
    (μc : Measure γ) [SFinite μb] [SFinite μc] :
    MeasurePreserving (MeasurableEquiv.prodAssoc : (α × β) × γ ≃ᵐ α × β × γ)
      ((μa.productBySections μb).productBySections μc)
        (μa.productBySections (μb.productBySections μc)) where
  measurable := MeasurableEquiv.prodAssoc.measurable
  map_eq := by
    ext s hs
    have A (x : α) : MeasurableSet (Prod.mk x ⁻¹' s) := measurable_prodMk_left hs
    have B : MeasurableSet (MeasurableEquiv.prodAssoc ⁻¹' s) :=
      MeasurableEquiv.prodAssoc.measurable hs
    rw [map_apply hs MeasurableEquiv.prodAssoc.measurable.aemeasurable,
      Measure.productBySections_apply (ν := μc) B,
      Measure.productBySections_apply (ν := μb.productBySections μc) hs,
      lintegral_productBySections _ (measurable_measure_prodMk_left B).aemeasurable]
    simp only [Measure.productBySections_apply, A]
    rfl

end MeasurePreserving

end MeasureTheory
