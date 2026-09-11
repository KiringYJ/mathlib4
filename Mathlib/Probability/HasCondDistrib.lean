/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/

module

public import Mathlib.Probability.HasLaw

import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# A predicate for having a specified conditional distribution

We introduce a predicate `HasCondDistrib Y X κ P` stating that the conditional distribution of `Y`
given `X` under the measure `P` is equal to the kernel `κ`.
The statement requires the pair `(X, Y)` to be a.e. measurable and says that its law under `P` is
equal to `(P.map X) ⊗ₘ κ`, the product of the law of `X` under `P` and the kernel `κ`.

## Main definitions

* `HasCondDistrib Y X κ P` : predicate stating that the conditional distribution of `Y` given `X`
  under the measure `P` is equal to the kernel `κ`.

-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω 𝓧 𝓨 𝓩 : Type*} {mΩ : SigmaAlgebra Ω}
  {m𝓧 : SigmaAlgebra 𝓧} {m𝓨 : SigmaAlgebra 𝓨} {m𝓩 : SigmaAlgebra 𝓩}
  {P : Measure Ω} {X : Ω → 𝓧} {Y : Ω → 𝓨} {κ : Kernel 𝓧 𝓨}

/-- Predicate stating that the conditional distribution of `Y` given `X` under the measure `P`
is equal to the kernel `κ`. -/
@[fun_prop]
structure HasCondDistrib (Y : Ω → 𝓨) (X : Ω → 𝓧) (κ : Kernel 𝓧 𝓨)
    (P : Measure Ω) : Prop where
  protected aemeasurable : AEMeasurable (fun ω ↦ (X ω, Y ω)) P := by fun_prop
  protected map_eq : P.map (fun ω ↦ (X ω, Y ω)) aemeasurable =
    P.map X aemeasurable.fst ⊗ₘ κ

attribute [fun_prop] HasCondDistrib.aemeasurable

@[fun_prop]
lemma HasCondDistrib.aemeasurable_fst (h : HasCondDistrib Y X κ P) :
    AEMeasurable X P := h.aemeasurable.fst

@[fun_prop]
lemma HasCondDistrib.aemeasurable_snd (h : HasCondDistrib Y X κ P) :
    AEMeasurable Y P := h.aemeasurable.snd

lemma HasLaw.prodMk_of_hasCondDistrib {Q : Measure 𝓧}
    (h1 : HasLaw X Q P) (h2 : HasCondDistrib Y X κ P) :
    HasLaw (fun ω ↦ (X ω, Y ω)) (Q ⊗ₘ κ) P where
  aemeasurable := h2.aemeasurable
  map_eq := by simpa only [h1.map_eq] using h2.map_eq

lemma HasCondDistrib.hasLaw_of_const [IsProbabilityMeasure P] {Q : Measure 𝓨} [SFinite Q]
    (h : HasCondDistrib Y X (Kernel.const 𝓧 Q) P) :
    HasLaw Y Q P where
  aemeasurable := h.aemeasurable_snd
  map_eq := by
    have h_snd : (P.map (fun ω ↦ (X ω, Y ω))).snd = Q := by
      rw [h.map_eq, Measure.snd_compProd]
      simp [Measure.map_apply (hf := h.aemeasurable_fst)]
    rwa [Measure.snd_map_prodMk₀ h.aemeasurable_fst (by fun_prop)] at h_snd

variable [SFinite P] [IsSFiniteKernel κ]

lemma HasCondDistrib.comp_left (h : HasCondDistrib Y X κ P) {f : 𝓨 → 𝓩} (hf : Measurable f) :
    HasCondDistrib (f ∘ Y) X (κ.map f) P := by
  have hpair := h.aemeasurable
  have hout := h.aemeasurable_fst.prodMk
    (h.aemeasurable_snd.comp_aemeasurable hf.aemeasurable)
  have hpmap : Measurable (Prod.map (id : 𝓧 → 𝓧) f) := measurable_id.prodMap hf
  have hcomp := hpair.comp_aemeasurable hpmap.aemeasurable
  have hfun : (fun ω ↦ (X ω, f (Y ω))) =ᵐ[P]
      Prod.map id f ∘ fun ω ↦ (X ω, Y ω) := ae_of_all _ fun _ ↦ rfl
  exact
  { aemeasurable := hout
    map_eq := calc
      P.map (fun ω ↦ (X ω, f (Y ω))) hout =
          (P.map (fun ω ↦ (X ω, Y ω)) hpair).map (Prod.map id f) hpmap.aemeasurable := by
        calc
          _ = P.map (Prod.map id f ∘ fun ω ↦ (X ω, Y ω)) hcomp :=
            Measure.map_congr hfun hout
          _ = _ := (Measure.map_map hpair hpmap.aemeasurable).symm
      _ = (P.map X h.aemeasurable_fst ⊗ₘ κ).map (Prod.map id f) hpmap.aemeasurable := by
        simp only [h.map_eq]
      _ = P.map X h.aemeasurable_fst ⊗ₘ κ.map f hf := (Measure.compProd_map hf).symm }

lemma HasCondDistrib.fst {Y : Ω → 𝓨 × 𝓩} {κ : Kernel 𝓧 (𝓨 × 𝓩)} [IsSFiniteKernel κ]
    (h : HasCondDistrib Y X κ P) :
    HasCondDistrib (fun ω ↦ (Y ω).1) X κ.fst P := by
  rw [Kernel.fst_eq]
  exact h.comp_left measurable_fst

lemma HasCondDistrib.snd {Y : Ω → 𝓨 × 𝓩} {κ : Kernel 𝓧 (𝓨 × 𝓩)} [IsSFiniteKernel κ]
    (h : HasCondDistrib Y X κ P) :
    HasCondDistrib (fun ω ↦ (Y ω).2) X κ.snd P := by
  rw [Kernel.snd_eq]
  exact h.comp_left measurable_snd

lemma HasCondDistrib.comp_right {f : 𝓩 → 𝓧}
    {hf : Measurable f} {Z : Ω → 𝓩} (h : HasCondDistrib Y Z (κ.comap f hf) P) :
    HasCondDistrib Y (f ∘ Z) κ P := by
  have hout := (h.aemeasurable_fst.comp_aemeasurable hf.aemeasurable).prodMk
    h.aemeasurable_snd
  have hpmap : Measurable (Prod.map f (id : 𝓨 → 𝓨)) := hf.prodMap measurable_id
  have hcomp := h.aemeasurable.comp_aemeasurable hpmap.aemeasurable
  have hfun : (fun a ↦ ((f ∘ Z) a, Y a)) =ᵐ[P]
      Prod.map f id ∘ fun a ↦ (Z a, Y a) := ae_of_all _ fun _ ↦ rfl
  exact
  { aemeasurable := hout
    map_eq := calc
      P.map (fun a ↦ ((f ∘ Z) a, Y a)) hout =
          (P.map (fun a ↦ (Z a, Y a)) h.aemeasurable).map
            (Prod.map f id) hpmap.aemeasurable := by
        calc
          _ = P.map (Prod.map f id ∘ fun a ↦ (Z a, Y a)) hcomp :=
            Measure.map_congr hfun hout
          _ = _ := (Measure.map_map h.aemeasurable hpmap.aemeasurable).symm
      _ = (P.map Z h.aemeasurable_fst ⊗ₘ κ.comap f hf).map
          (Prod.map f id) hpmap.aemeasurable := by simp only [h.map_eq]
      _ = (P.map Z h.aemeasurable_fst).map f hf.aemeasurable ⊗ₘ κ := by
        ext s hs
        rw [Measure.map_apply hs hpmap.aemeasurable, Measure.compProd_apply (by measurability),
          Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
        rfl
      _ = P.map (f ∘ Z) (h.aemeasurable_fst.comp_aemeasurable hf.aemeasurable) ⊗ₘ κ := by
        rw [Measure.map_map h.aemeasurable_fst hf.aemeasurable] }

lemma HasCondDistrib.measurableEquiv_comp_right (h : HasCondDistrib Y X κ P) (f : 𝓧 ≃ᵐ 𝓩) :
    HasCondDistrib Y (f ∘ X) (κ.comap f.symm f.symm.measurable) P := by
  apply HasCondDistrib.comp_right (hf := f.measurable)
  simpa [← Kernel.comap_comp_right]

lemma HasCondDistrib.of_compProd {Z : Ω → 𝓩} {η : Kernel (𝓧 × 𝓨) 𝓩} [IsMarkovKernel η]
    (h : HasCondDistrib (fun a ↦ (Y a, Z a)) X (κ ⊗ₖ η) P) :
    HasCondDistrib Z (fun a ↦ (X a, Y a)) η P := by
  have hZ : AEMeasurable Z P := h.aemeasurable_snd.snd
  have hY : AEMeasurable Y P := h.aemeasurable_snd.fst
  have hX : AEMeasurable X P := h.aemeasurable_fst
  have hXY := hX.prodMk hY
  have hout := hXY.prodMk hZ
  have hassoc : AEMeasurable MeasurableEquiv.prodAssoc.symm
      (P.map (fun a ↦ (X a, (Y a, Z a))) h.aemeasurable) := by fun_prop
  have hcomp := h.aemeasurable.comp_aemeasurable hassoc
  have hfun : (fun a ↦ ((X a, Y a), Z a)) =ᵐ[P]
      MeasurableEquiv.prodAssoc.symm ∘ fun a ↦ (X a, (Y a, Z a)) := ae_of_all _ fun _ ↦ rfl
  refine ⟨hout, ?_⟩
  calc
    P.map (fun a ↦ ((X a, Y a), Z a)) hout =
        (P.map (fun a ↦ (X a, (Y a, Z a))) h.aemeasurable).map
          MeasurableEquiv.prodAssoc.symm (by fun_prop) := by
      calc
        _ = P.map (MeasurableEquiv.prodAssoc.symm ∘ fun a ↦ (X a, (Y a, Z a))) hcomp :=
          Measure.map_congr hfun hout
        _ = _ := (Measure.map_map h.aemeasurable hassoc).symm
    _ = (P.map X hX ⊗ₘ (κ ⊗ₖ η)).map MeasurableEquiv.prodAssoc.symm (by fun_prop) := by
      simp only [h.map_eq]
    _ = (P.map X hX ⊗ₘ κ) ⊗ₘ η := Measure.compProd_assoc
    _ = P.map (fun a ↦ (X a, Y a)) hXY ⊗ₘ η := by
      congr 1
      simpa only [Kernel.fst_compProd] using h.fst.map_eq.symm

end ProbabilityTheory
