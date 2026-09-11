/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Probability.Independence.Basic

/-!
# Probability density function

This file defines the probability density function of random variables, by which we mean
measurable functions taking values in a Borel space. The probability density function is defined
as the Radon–Nikodym derivative of the law of `X`. In particular, a measurable function `f`
is said to the probability density function of a random variable `X` if for all measurable
sets `S`, `ℙ(X ∈ S) = ∫ x in S, f x dx`. Probability density functions are one way of describing
the distribution of a random variable, and are useful for calculating probabilities and
finding moments (although the latter is better achieved with moment-generating functions).

This file also defines the continuous uniform distribution and proves some properties about
random variables with this distribution.

## Main definitions

* `MeasureTheory.HasPDF` : A random variable `X : Ω → E` is said to `HasPDF` with
  respect to the measure `ℙ` on `Ω` and `μ` on `E` if the push-forward measure of `ℙ` along `X`
  is absolutely continuous with respect to `μ` and they `HaveLebesgueDecomposition`.
* `MeasureTheory.pdf` : If `X` is a random variable that `HasPDF X ℙ μ`, then `pdf X`
  is the Radon–Nikodym derivative of the push-forward measure of `ℙ` along `X` with respect to `μ`.
* `MeasureTheory.pdf.IsUniform` : A random variable `X` is said to follow the uniform
  distribution if it has a constant probability density function with a compact, non-null support.

## Main results

* `MeasureTheory.pdf.integral_pdf_smul` : Law of the unconscious statistician,
  i.e. if a random variable `X : Ω → E` has pdf `f`, then `𝔼(g(X)) = ∫ x, f x • g x dx` for
  all measurable `g : E → F`.
* `MeasureTheory.pdf.integral_mul_eq_integral` : A real-valued random variable `X` with
  pdf `f` has expectation `∫ x, x * f x dx`.
* `MeasureTheory.pdf.IsUniform.integral_eq` : If `X` follows the uniform distribution with
  its pdf having support `s`, then `X` has expectation `(λ s)⁻¹ * ∫ x in s, x dx` where `λ`
  is the Lebesgue measure.
-/

@[expose] public section


open scoped MeasureTheory NNReal ENNReal

open TopologicalSpace MeasureTheory Measure ProbabilityTheory

noncomputable section

namespace MeasureTheory

variable {Ω E : Type*} [SigmaAlgebra E]

/-- A random variable `X : Ω → E` is said to have a probability density function (`HasPDF`)
with respect to the measure `ℙ` on `Ω` and `μ` on `E`
if the push-forward measure of `ℙ` along `X` is absolutely continuous with respect to `μ`
and they have a Lebesgue decomposition (`HaveLebesgueDecomposition`). -/
class HasPDF {m : SigmaAlgebra Ω} (X : Ω → E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac) :
    Prop where
  protected aemeasurable' : AEMeasurable X ℙ
  protected haveLebesgueDecomposition' :
    (map X ℙ aemeasurable').HaveLebesgueDecomposition μ
  protected absolutelyContinuous' : map X ℙ aemeasurable' ≪ μ

attribute [fun_prop] HasPDF.aemeasurable'

section HasPDF

variable {_ : SigmaAlgebra Ω} {X Y : Ω → E} {ℙ : Measure Ω} {μ : Measure E}

theorem hasPDF_iff :
    HasPDF X ℙ μ ↔ ∃ hX : AEMeasurable X ℙ,
      (map X ℙ hX).HaveLebesgueDecomposition μ ∧ map X ℙ hX ≪ μ :=
  ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

theorem hasPDF_iff_of_aemeasurable (hX : AEMeasurable X ℙ) :
    HasPDF X ℙ μ ↔ (map X ℙ hX).HaveLebesgueDecomposition μ ∧ map X ℙ hX ≪ μ := by
  rw [hasPDF_iff]
  constructor
  · rintro ⟨_, hld, hac⟩
    exact ⟨hld, hac⟩
  · rintro ⟨hld, hac⟩
    exact ⟨hX, hld, hac⟩

variable (X ℙ μ) in
@[fun_prop] theorem HasPDF.aemeasurable [HasPDF X ℙ μ] : AEMeasurable X ℙ :=
  HasPDF.aemeasurable' μ

instance HasPDF.haveLebesgueDecomposition [HasPDF X ℙ μ] :
    (map X ℙ (HasPDF.aemeasurable X ℙ μ)).HaveLebesgueDecomposition μ :=
  HasPDF.haveLebesgueDecomposition'

theorem HasPDF.absolutelyContinuous [HasPDF X ℙ μ] :
    map X ℙ (HasPDF.aemeasurable X ℙ μ) ≪ μ :=
  HasPDF.absolutelyContinuous'

/-- A random variable that `HasPDF` is quasi-measure-preserving. -/
theorem HasPDF.quasiMeasurePreserving_of_measurable (X : Ω → E) (ℙ : Measure Ω) (μ : Measure E)
    [HasPDF X ℙ μ] (h : Measurable X) : QuasiMeasurePreserving X ℙ μ :=
  { measurable := h
    absolutelyContinuous := HasPDF.absolutelyContinuous .. }

theorem HasPDF.congr (hXY : X =ᵐ[ℙ] Y) [hX : HasPDF X ℙ μ] : HasPDF Y ℙ μ :=
  ⟨(HasPDF.aemeasurable X ℙ μ).congr hXY,
    ℙ.map_congr hXY (HasPDF.aemeasurable X ℙ μ) ▸ hX.haveLebesgueDecomposition,
    ℙ.map_congr hXY (HasPDF.aemeasurable X ℙ μ) ▸ hX.absolutelyContinuous⟩

theorem HasPDF.congr_iff (hXY : X =ᵐ[ℙ] Y) : HasPDF X ℙ μ ↔ HasPDF Y ℙ μ :=
  ⟨fun _ ↦ HasPDF.congr hXY, fun _ ↦ HasPDF.congr hXY.symm⟩

/-- X `HasPDF` if there is a pdf `f` such that `map X ℙ = μ.withDensity f`. -/
theorem hasPDF_of_map_eq_withDensity (hX : AEMeasurable X ℙ) (f : E → ℝ≥0∞) (hf : AEMeasurable f μ)
    (h : map X ℙ hX = μ.withDensity f) : HasPDF X ℙ μ := by
  refine ⟨hX, ?_, ?_⟩ <;> rw [h]
  · rw [withDensity_congr_ae hf.ae_eq_mk]
    exact haveLebesgueDecomposition_withDensity μ hf.measurable_mk
  · exact withDensity_absolutelyContinuous μ f

end HasPDF

/-- If `X` is a random variable, then `pdf X ℙ μ`
is the Radon–Nikodym derivative of the push-forward measure of `ℙ` along `X` with respect to `μ`. -/
def pdf {_ : SigmaAlgebra Ω} (X : Ω → E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac)
    (hX : AEMeasurable X ℙ := by fun_prop) : E → ℝ≥0∞ :=
  (map X ℙ hX).rnDeriv μ

theorem pdf_def {_ : SigmaAlgebra Ω} {ℙ : Measure Ω} {μ : Measure E} {X : Ω → E}
    (hX : AEMeasurable X ℙ := by fun_prop) :
    pdf X ℙ μ hX = (map X ℙ hX).rnDeriv μ := rfl

theorem pdf_of_not_haveLebesgueDecomposition {_ : SigmaAlgebra Ω} {ℙ : Measure Ω}
    {μ : Measure E} {X : Ω → E} (hX : AEMeasurable X ℙ)
    (h : ¬(map X ℙ hX).HaveLebesgueDecomposition μ) : pdf X ℙ μ hX = 0 :=
  rnDeriv_of_not_haveLebesgueDecomposition h

@[fun_prop]
theorem measurable_pdf {m : SigmaAlgebra Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) (hX : AEMeasurable X ℙ := by fun_prop) :
    Measurable (pdf X ℙ μ hX) := by
  exact measurable_rnDeriv _ _

theorem withDensity_pdf_le_map {_ : SigmaAlgebra Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) (hX : AEMeasurable X ℙ := by fun_prop) :
    μ.withDensity (pdf X ℙ μ hX) ≤ map X ℙ hX :=
  withDensity_rnDeriv_le _ _

theorem setLIntegral_pdf_le_map {m : SigmaAlgebra Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) (s : Set E) (hX : AEMeasurable X ℙ := by fun_prop) :
    ∫⁻ x in s, pdf X ℙ μ hX x ∂μ ≤ (map X ℙ hX) s := by
  apply (withDensity_apply_le _ s).trans
  exact withDensity_pdf_le_map X ℙ μ hX s

theorem map_eq_withDensity_pdf {m : SigmaAlgebra Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) [hX : HasPDF X ℙ μ] :
    map X ℙ (HasPDF.aemeasurable X ℙ μ) =
      μ.withDensity (pdf X ℙ μ (HasPDF.aemeasurable X ℙ μ)) := by
  rw [pdf, withDensity_rnDeriv_eq _ _ hX.absolutelyContinuous]

theorem map_eq_setLIntegral_pdf {m : SigmaAlgebra Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) [hX : HasPDF X ℙ μ] {s : Set E}
    (hs : MeasurableSet s) : (map X ℙ (HasPDF.aemeasurable X ℙ μ)) s =
      ∫⁻ x in s, pdf X ℙ μ (HasPDF.aemeasurable X ℙ μ) x ∂μ := by
  rw [← withDensity_apply _ hs, map_eq_withDensity_pdf X ℙ μ]

namespace pdf

variable {m : SigmaAlgebra Ω} {ℙ : Measure Ω} {μ : Measure E}

protected theorem congr {X Y : Ω → E} (hX : AEMeasurable X ℙ) (hXY : X =ᵐ[ℙ] Y) :
    pdf X ℙ μ hX = pdf Y ℙ μ (hX.congr hXY) := by
  rw [pdf, pdf, map_congr hXY hX]

theorem lintegral_eq_measure_univ {X : Ω → E} [HasPDF X ℙ μ] :
    ∫⁻ x, pdf X ℙ μ (HasPDF.aemeasurable X ℙ μ) x ∂μ = ℙ Set.univ := by
  rw [← setLIntegral_univ, ← map_eq_setLIntegral_pdf X ℙ μ MeasurableSet.univ,
    map_apply MeasurableSet.univ (HasPDF.aemeasurable X ℙ μ), Set.preimage_univ]

theorem eq_of_map_eq_withDensity [IsFiniteMeasure ℙ] {X : Ω → E} [HasPDF X ℙ μ] (f : E → ℝ≥0∞)
    (hmf : AEMeasurable f μ) :
    map X ℙ (HasPDF.aemeasurable X ℙ μ) = μ.withDensity f ↔
      pdf X ℙ μ (HasPDF.aemeasurable X ℙ μ) =ᵐ[μ] f := by
  rw [map_eq_withDensity_pdf X ℙ μ]
  apply withDensity_eq_iff
    (measurable_pdf X ℙ μ (HasPDF.aemeasurable X ℙ μ)).aemeasurable hmf
  rw [lintegral_eq_measure_univ]
  exact measure_ne_top _ _

theorem eq_of_map_eq_withDensity' [SigmaFinite μ] {X : Ω → E} [HasPDF X ℙ μ] (f : E → ℝ≥0∞)
    (hmf : AEMeasurable f μ) :
    map X ℙ (HasPDF.aemeasurable X ℙ μ) = μ.withDensity f ↔
      pdf X ℙ μ (HasPDF.aemeasurable X ℙ μ) =ᵐ[μ] f :=
  map_eq_withDensity_pdf X ℙ μ ▸
    withDensity_eq_iff_of_sigmaFinite
      (measurable_pdf X ℙ μ (HasPDF.aemeasurable X ℙ μ)).aemeasurable hmf

nonrec theorem ae_lt_top [IsFiniteMeasure ℙ] {μ : Measure E} {X : Ω → E}
    (hX : AEMeasurable X ℙ) : ∀ᵐ x ∂μ, pdf X ℙ μ hX x < ∞ :=
  rnDeriv_lt_top (map X ℙ hX) μ

nonrec theorem ofReal_toReal_ae_eq [IsFiniteMeasure ℙ] {X : Ω → E}
    (hX : AEMeasurable X ℙ) :
    (fun x => ENNReal.ofReal (pdf X ℙ μ hX x).toReal) =ᵐ[μ] pdf X ℙ μ hX :=
  ofReal_toReal_ae_eq (ae_lt_top hX)

section IntegralPDFMul

/-- **The Law of the Unconscious Statistician** for nonnegative random variables. -/
theorem lintegral_pdf_mul {X : Ω → E} [HasPDF X ℙ μ] {f : E → ℝ≥0∞}
    (hf : AEMeasurable f μ) :
    ∫⁻ x, pdf X ℙ μ (HasPDF.aemeasurable X ℙ μ) x * f x ∂μ = ∫⁻ x, f (X x) ∂ℙ := by
  rw [pdf,
    ← lintegral_map' (HasPDF.aemeasurable X ℙ μ) (hf.mono_ac HasPDF.absolutelyContinuous),
    lintegral_rnDeriv_mul HasPDF.absolutelyContinuous hf]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem integrable_pdf_smul_iff [IsFiniteMeasure ℙ] {X : Ω → E} [HasPDF X ℙ μ] {f : E → F}
    (hf : AEStronglyMeasurable f μ) :
    Integrable (fun x => (pdf X ℙ μ (HasPDF.aemeasurable X ℙ μ) x).toReal • f x) μ ↔
      Integrable (fun x => f (X x)) ℙ := by
  rw [← Function.comp_def,
    ← integrable_map_measure (HasPDF.aemeasurable X ℙ μ)
      (hf.mono_ac HasPDF.absolutelyContinuous),
    map_eq_withDensity_pdf X ℙ μ, pdf, integrable_rnDeriv_smul_iff HasPDF.absolutelyContinuous]
  rw [withDensity_rnDeriv_eq _ _ HasPDF.absolutelyContinuous]

/-- **The Law of the Unconscious Statistician**: Given a random variable `X` and a measurable
function `f`, `f ∘ X` is a random variable with expectation `∫ x, pdf X x • f x ∂μ`
where `μ` is a measure on the codomain of `X`. -/
theorem integral_pdf_smul [IsFiniteMeasure ℙ] {X : Ω → E} [HasPDF X ℙ μ] {f : E → F}
    (hf : AEStronglyMeasurable f μ) :
    ∫ x, (pdf X ℙ μ (HasPDF.aemeasurable X ℙ μ) x).toReal • f x ∂μ =
      ∫ x, f (X x) ∂ℙ := by
  rw [← integral_map (HasPDF.aemeasurable X ℙ μ) (hf.mono_ac HasPDF.absolutelyContinuous),
    map_eq_withDensity_pdf X ℙ μ, pdf, integral_rnDeriv_smul HasPDF.absolutelyContinuous,
    withDensity_rnDeriv_eq _ _ HasPDF.absolutelyContinuous]

end IntegralPDFMul

section

variable {F : Type*} [SigmaAlgebra F] {ν : Measure F} (X : Ω → E) [HasPDF X ℙ μ] {g : E → F}

/-- A random variable that `HasPDF` transformed under a `QuasiMeasurePreserving`
map also `HasPDF` if `(map g (map X ℙ)).HaveLebesgueDecomposition μ`.

`quasiMeasurePreserving_hasPDF` is more useful in the case we are working with a
probability measure and a real-valued random variable. -/
theorem quasiMeasurePreserving_hasPDF (hg : QuasiMeasurePreserving g μ ν)
    (hmap : (map g (map X ℙ (HasPDF.aemeasurable X ℙ μ))
      (hg.aemeasurable.mono_ac HasPDF.absolutelyContinuous)).HaveLebesgueDecomposition ν) :
    HasPDF (g ∘ X) ℙ ν := by
  have hgm : AEMeasurable g (map X ℙ (HasPDF.aemeasurable X ℙ μ)) :=
    hg.aemeasurable.mono_ac HasPDF.absolutelyContinuous
  rw [hasPDF_iff_of_aemeasurable
    (hg.measurable.comp_aemeasurable (HasPDF.aemeasurable X ℙ μ)),
    ← Measure.map_map (HasPDF.aemeasurable X ℙ μ) hgm]
  refine ⟨hmap, ?_⟩
  exact (HasPDF.absolutelyContinuous.map hg.1).trans hg.2

theorem quasiMeasurePreserving_hasPDF' [SFinite ℙ] [SigmaFinite ν]
    (hg : QuasiMeasurePreserving g μ ν) : HasPDF (g ∘ X) ℙ ν :=
  quasiMeasurePreserving_hasPDF X hg inferInstance

end

section Real

variable {X : Ω → ℝ}

nonrec theorem _root_.Real.hasPDF_iff [SFinite ℙ] :
    HasPDF X ℙ ↔ ∃ hX : AEMeasurable X ℙ, map X ℙ hX ≪ volume := by
  rw [hasPDF_iff]
  simp only [and_iff_right (inferInstance : HaveLebesgueDecomposition _ _)]

/-- A real-valued random variable `X` `HasPDF X ℙ λ` (where `λ` is the Lebesgue measure) if and
only if the push-forward measure of `ℙ` along `X` is absolutely continuous with respect to `λ`. -/
nonrec theorem _root_.Real.hasPDF_iff_of_aemeasurable [SFinite ℙ] (hX : AEMeasurable X ℙ) :
    HasPDF X ℙ ↔ map X ℙ hX ≪ volume := by
  rw [MeasureTheory.hasPDF_iff_of_aemeasurable hX,
    and_iff_right (inferInstance : HaveLebesgueDecomposition _ _)]

variable [IsFiniteMeasure ℙ]

/-- If `X` is a real-valued random variable that has pdf `f`, then the expectation of `X` equals
`∫ x, x * f x ∂λ` where `λ` is the Lebesgue measure. -/
theorem integral_mul_eq_integral [HasPDF X ℙ] :
    ∫ x, x * (pdf X ℙ volume (HasPDF.aemeasurable X ℙ volume) x).toReal = ∫ x, X x ∂ℙ :=
  calc
    _ = ∫ x, (pdf X ℙ volume (HasPDF.aemeasurable X ℙ volume) x).toReal * x := by
      congr with x
      exact mul_comm _ _
    _ = _ := integral_pdf_smul measurable_id.aestronglyMeasurable

theorem hasFiniteIntegral_mul {f : ℝ → ℝ} {g : ℝ → ℝ≥0∞} (hX : AEMeasurable X ℙ)
    (hg : pdf X ℙ volume hX =ᵐ[volume] g)
    (hgi : ∫⁻ x, ‖f x‖ₑ * g x ≠ ∞) :
    HasFiniteIntegral fun x => f x * (pdf X ℙ volume hX x).toReal := by
  rw [hasFiniteIntegral_iff_enorm]
  have : (fun x => ‖f x‖ₑ * g x) =ᵐ[volume]
      fun x => ‖f x * (pdf X ℙ volume hX x).toReal‖ₑ := by
    refine ae_eq_trans
      ((ae_eq_refl _).fun_mul (ae_eq_trans hg.symm (ofReal_toReal_ae_eq hX).symm)) ?_
    simp_rw [← smul_eq_mul, enorm_smul, smul_eq_mul]
    refine .fun_mul (ae_eq_refl _) ?_
    simp only [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ae_eq_refl]
  rwa [lt_top_iff_ne_top, ← lintegral_congr_ae this]

end Real

section TwoVariables

variable {F : Type*} [SigmaAlgebra F] {ν : Measure F} {X : Ω → E} {Y : Ω → F}

/-- Random variables are independent iff their joint density is a product of marginal densities. -/
theorem indepFun_iff_pdf_prod_eq_pdf_mul_pdf
    [IsFiniteMeasure ℙ] [SigmaFinite μ] [SigmaFinite ν] [HasPDF (fun ω ↦ (X ω, Y ω)) ℙ (μ.prod ν)] :
    IndepFun X Y ℙ ↔
      pdf (fun ω ↦ (X ω, Y ω)) ℙ (μ.prod ν)
          (HasPDF.aemeasurable (fun ω ↦ (X ω, Y ω)) ℙ (μ.prod ν)) =ᵐ[μ.prod ν]
        fun z ↦ pdf X ℙ μ (HasPDF.aemeasurable (fun ω ↦ (X ω, Y ω)) ℙ (μ.prod ν)).fst
          z.1 * pdf Y ℙ ν
            (HasPDF.aemeasurable (fun ω ↦ (X ω, Y ω)) ℙ (μ.prod ν)).snd z.2 := by
  have : HasPDF X ℙ μ := quasiMeasurePreserving_hasPDF'
    (μ := μ.prod ν Measurable.map_prodMk_left.aemeasurable) (fun ω ↦ (X ω, Y ω))
    quasiMeasurePreserving_fst
  have : HasPDF Y ℙ ν := quasiMeasurePreserving_hasPDF'
    (μ := μ.prod ν Measurable.map_prodMk_left.aemeasurable) (fun ω ↦ (X ω, Y ω))
    quasiMeasurePreserving_snd
  have h₀ : (ℙ.map X (HasPDF.aemeasurable X ℙ μ)).prod
      (ℙ.map Y (HasPDF.aemeasurable Y ℙ ν)) =
      (μ.prod ν).withDensity fun z ↦
        pdf X ℙ μ (HasPDF.aemeasurable X ℙ μ) z.1 *
          pdf Y ℙ ν (HasPDF.aemeasurable Y ℙ ν) z.2 :=
    prod_eq fun s t hs ht ↦ by rw [withDensity_apply _ (hs.prod ht), ← prod_restrict,
      lintegral_prod_mul
        (measurable_pdf X ℙ μ (HasPDF.aemeasurable X ℙ μ)).aemeasurable
        (measurable_pdf Y ℙ ν (HasPDF.aemeasurable Y ℙ ν)).aemeasurable,
      map_eq_setLIntegral_pdf X ℙ μ hs, map_eq_setLIntegral_pdf Y ℙ ν ht]
  rw [indepFun_iff_map_prod_eq_prod_map_map (HasPDF.aemeasurable X ℙ μ) (HasPDF.aemeasurable Y ℙ ν),
    ← eq_of_map_eq_withDensity, h₀]
  exact (((measurable_pdf X ℙ μ (HasPDF.aemeasurable X ℙ μ)).comp measurable_fst).mul
    ((measurable_pdf Y ℙ ν (HasPDF.aemeasurable Y ℙ ν)).comp measurable_snd)).aemeasurable

end TwoVariables

end pdf

end MeasureTheory

section Group

namespace ProbabilityTheory

variable {Ω G : Type*} {mΩ : SigmaAlgebra Ω} {ℙ : Measure Ω} [Group G] {mG : SigmaAlgebra G}
  [MeasurableMul₂ G] [MeasurableInv G] {μ : Measure G} [IsMulLeftInvariant μ] {X Y : Ω → G}

@[to_additive]
theorem IndepFun.mul_hasPDF' [SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ]
    (σX : SigmaFinite (ℙ.map X (HasPDF.aemeasurable X ℙ μ)))
    (σY : SigmaFinite (ℙ.map Y (HasPDF.aemeasurable Y ℙ μ))) (hXY : IndepFun X Y ℙ) :
    HasPDF (X * Y) ℙ μ := by
  have : AEMeasurable X ℙ := HasPDF.aemeasurable' μ
  have : AEMeasurable Y ℙ := HasPDF.aemeasurable' μ
  rw [hasPDF_iff_of_aemeasurable (by fun_prop),
    hXY.map_mul_eq_map_mconv_map₀' (by fun_prop) (by fun_prop) σX σY]
  refine ⟨?_, mconv_absolutelyContinuous HasPDF.absolutelyContinuous⟩
  apply HaveLebesgueDecomposition.mconv <;> exact HasPDF.absolutelyContinuous

@[to_additive]
theorem IndepFun.mul_hasPDF [SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ] [IsFiniteMeasure ℙ]
  (hXY : IndepFun X Y ℙ) : HasPDF (X * Y) ℙ μ := by
  apply hXY.mul_hasPDF' <;> apply IsFiniteMeasure.toSigmaFinite

@[to_additive]
theorem IndepFun.pdf_mul_eq_mlconvolution_pdf' [SigmaFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ]
    (σX : SigmaFinite (ℙ.map X (HasPDF.aemeasurable X ℙ μ)))
    (σY : SigmaFinite (ℙ.map Y (HasPDF.aemeasurable Y ℙ μ))) (hXY : IndepFun X Y ℙ) :
    pdf (X * Y) ℙ μ ((HasPDF.aemeasurable X ℙ μ).mul (HasPDF.aemeasurable Y ℙ μ)) =ᵐ[μ]
      pdf X ℙ μ (HasPDF.aemeasurable X ℙ μ) ⋆ₘₗ[μ]
        pdf Y ℙ μ (HasPDF.aemeasurable Y ℙ μ) := by
  rw [pdf, hXY.map_mul_eq_map_mconv_map₀' (HasPDF.aemeasurable' μ) (HasPDF.aemeasurable' μ) σX σY]
  apply rnDeriv_mconv' <;> exact HasPDF.absolutelyContinuous

@[to_additive]
theorem IndepFun.pdf_mul_eq_mlconvolution_pdf [SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ]
    [IsFiniteMeasure ℙ] (hXY : IndepFun X Y ℙ) :
    pdf (X * Y) ℙ μ ((HasPDF.aemeasurable X ℙ μ).mul (HasPDF.aemeasurable Y ℙ μ)) =ᵐ[μ]
      pdf X ℙ μ (HasPDF.aemeasurable X ℙ μ) ⋆ₘₗ[μ]
        pdf Y ℙ μ (HasPDF.aemeasurable Y ℙ μ) := by
  rw [pdf, hXY.map_mul_eq_map_mconv_map₀ (HasPDF.aemeasurable' μ) (HasPDF.aemeasurable' μ)]
  apply rnDeriv_mconv <;> exact HasPDF.absolutelyContinuous

end ProbabilityTheory

end Group
