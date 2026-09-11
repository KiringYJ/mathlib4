/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Equip `ℂ` with the Borel sigma-algebra -/

public section


noncomputable section

instance (priority := 900) RCLike.sigmaAlgebra {𝕜 : Type*} [RCLike 𝕜] : SigmaAlgebra 𝕜 :=
  borel 𝕜

instance (priority := 900) RCLike.borelSpace {𝕜 : Type*} [RCLike 𝕜] : BorelSpace 𝕜 :=
  ⟨rfl⟩

instance Complex.sigmaAlgebra : SigmaAlgebra ℂ :=
  borel ℂ

instance Complex.borelSpace : BorelSpace ℂ :=
  ⟨rfl⟩
