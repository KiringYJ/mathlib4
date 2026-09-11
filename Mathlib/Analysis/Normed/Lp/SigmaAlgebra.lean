/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Sigma-algebra on `WithLp`

The sigma-algebra on `WithLp p X` is the one transported from `X`.
-/

@[expose] public section

open scoped ENNReal

variable (p : ℝ≥0∞) (X : Type*) [SigmaAlgebra X]

namespace WithLp

instance sigmaAlgebra : SigmaAlgebra (WithLp p X) :=
  SigmaAlgebra.comap ofLp inferInstance

@[fun_prop]
lemma measurable_ofLp : Measurable (@ofLp p X) := comap_measurable _

@[fun_prop]
lemma measurable_toLp : Measurable (@toLp p X) := fun s hs ↦ by
  obtain ⟨t, ht, rfl⟩ := hs
  simpa [Set.preimage_preimage]

variable (Y : Type*) [SigmaAlgebra Y] [TopologicalSpace X] [TopologicalSpace Y]
  [BorelSpace X] [BorelSpace Y] [SecondCountableTopologyEither X Y]

instance borelSpace : BorelSpace (WithLp p (X × Y)) where
  sigmaAlgebra_eq := by
    rw [instProdTopologicalSpace, borel_comap, sigmaAlgebra,
      BorelSpace.sigmaAlgebra_eq (α := X × Y)]

end WithLp

namespace PiLp

variable {ι : Type*} {X : ι → Type*} [Countable ι] [∀ i, SigmaAlgebra (X i)]
    [∀ i, TopologicalSpace (X i)] [∀ i, BorelSpace (X i)] [∀ i, SecondCountableTopology (X i)]

instance borelSpace : BorelSpace (PiLp p X) where
  sigmaAlgebra_eq := by
    rw [topologicalSpace, borel_comap, WithLp.sigmaAlgebra,
      BorelSpace.sigmaAlgebra_eq (α := Π i, X i)]

end PiLp

namespace MeasurableEquiv

/-- The map from `X` to `WithLp p X` as a measurable equivalence. -/
protected def toLp : X ≃ᵐ (WithLp p X) where
  toEquiv := (WithLp.equiv p X).symm
  measurable_toFun := WithLp.measurable_toLp p X
  measurable_invFun := WithLp.measurable_ofLp p X

lemma coe_toLp : ⇑(MeasurableEquiv.toLp p X) = WithLp.toLp p := rfl

lemma coe_toLp_symm : ⇑(MeasurableEquiv.toLp p X).symm = WithLp.ofLp := rfl

@[simp]
lemma toLp_apply (x : X) : MeasurableEquiv.toLp p X x = WithLp.toLp p x := rfl

@[simp]
lemma toLp_symm_apply (x : WithLp p X) :
    (MeasurableEquiv.toLp p X).symm x = WithLp.ofLp x := rfl

end MeasurableEquiv
