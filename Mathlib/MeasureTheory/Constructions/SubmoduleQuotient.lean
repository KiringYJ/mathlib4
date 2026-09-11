/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.MeasureTheory.SigmaAlgebra.Constructions

/-!
# Measurability on the quotient of a module by a submodule
-/

public section

namespace Submodule.Quotient
variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {p : Submodule R M}

instance [SigmaAlgebra M] : SigmaAlgebra (M ⧸ p) := Quotient.instSigmaAlgebra
instance [SigmaAlgebra M] [DiscreteSigmaAlgebra M] : DiscreteSigmaAlgebra (M ⧸ p) :=
  Quotient.instDiscreteSigmaAlgebra

end Submodule.Quotient
