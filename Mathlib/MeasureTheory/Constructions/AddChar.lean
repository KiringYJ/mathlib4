/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.MeasureTheory.SigmaAlgebra.Defs

/-!
# Measurable space instance for additive characters

This file endows `AddChar A M` with the discrete measurable space structure whenever `A` is a finite
discrete measurable space.

## TODO

Give the definition in the correct generality.
-/

public section

namespace AddChar
variable {A M : Type*} [AddMonoid A] [Monoid M] [SigmaAlgebra A] [SigmaAlgebra M]

@[nolint unusedArguments]
instance instSigmaAlgebra [DiscreteSigmaAlgebra A] [Finite A] :
    SigmaAlgebra (AddChar A M) :=
  ⊤

instance instDiscreteSigmaAlgebra [DiscreteSigmaAlgebra A] [Finite A] :
    DiscreteSigmaAlgebra (AddChar A M) :=
  ⟨fun _ ↦ trivial⟩

end AddChar
