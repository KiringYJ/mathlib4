/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.SigmaAlgebra.Defs
public import Mathlib.GroupTheory.GroupAction.IterateAct
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.ZMod.Defs

/-!
# Sigma-algebra typeclass instances

This file provides sigma-algebra instances for a selection of standard countable types,
in each case defining the sigma-algebra to be `⊤` (the discrete sigma-algebra).
-/

public section

instance Empty.instSigmaAlgebra : SigmaAlgebra Empty := ⊤

instance PUnit.instSigmaAlgebra : SigmaAlgebra PUnit := ⊤

instance Bool.instSigmaAlgebra : SigmaAlgebra Bool := ⊤

instance Prop.instSigmaAlgebra : SigmaAlgebra Prop := ⊤

instance Nat.instSigmaAlgebra : SigmaAlgebra ℕ := ⊤

instance ENat.instSigmaAlgebra : SigmaAlgebra ℕ∞ := ⊤

instance Fin.instSigmaAlgebra (n : ℕ) : SigmaAlgebra (Fin n) := ⊤

instance ZMod.instSigmaAlgebra (n : ℕ) : SigmaAlgebra (ZMod n) := ⊤

instance Int.instSigmaAlgebra : SigmaAlgebra ℤ := ⊤

instance Rat.instSigmaAlgebra : SigmaAlgebra ℚ := ⊤

@[to_additive]
instance IterateMulAct.instSigmaAlgebra {α : Type*} {f : α → α} :
    SigmaAlgebra (IterateMulAct f) := ⊤

@[to_additive]
instance IterateMulAct.instDiscreteSigmaAlgebra {α : Type*} {f : α → α} :
    DiscreteSigmaAlgebra (IterateMulAct f) := inferInstance

instance (priority := 100) Subsingleton.measurableSingletonClass
    {α} [SigmaAlgebra α] [Subsingleton α] : MeasurableSingletonClass α := by
  refine ⟨fun i => ?_⟩
  convert! MeasurableSet.univ
  simp [Set.eq_univ_iff_forall, eq_iff_true_of_subsingleton]

instance Bool.instMeasurableSingletonClass : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩

instance Prop.instMeasurableSingletonClass : MeasurableSingletonClass Prop := ⟨fun _ => trivial⟩

instance Nat.instMeasurableSingletonClass : MeasurableSingletonClass ℕ := ⟨fun _ => trivial⟩

instance ENat.instDiscreteSigmaAlgebra : DiscreteSigmaAlgebra ℕ∞ := ⟨fun _ ↦ trivial⟩

instance ENat.instMeasurableSingletonClass : MeasurableSingletonClass ℕ∞ := inferInstance

instance Fin.instMeasurableSingletonClass (n : ℕ) : MeasurableSingletonClass (Fin n) :=
  ⟨fun _ => trivial⟩

instance ZMod.instMeasurableSingletonClass (n : ℕ) : MeasurableSingletonClass (ZMod n) :=
  ⟨fun _ => trivial⟩

instance Int.instMeasurableSingletonClass : MeasurableSingletonClass ℤ := ⟨fun _ => trivial⟩

instance Rat.instMeasurableSingletonClass : MeasurableSingletonClass ℚ := ⟨fun _ => trivial⟩
