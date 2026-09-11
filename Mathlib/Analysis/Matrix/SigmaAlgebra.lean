/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Instances.Matrix

/-!
# Sigma-algebra on matrices

The sigma-algebra on `Matrix m n α` is the one transported from `m → n → α`.
-/

@[expose] public section

namespace Matrix

section SigmaAlgebra

variable {m n α : Type*} [SigmaAlgebra α]

instance : SigmaAlgebra (Matrix m n α) := inferInstanceAs <| SigmaAlgebra (m → n → α)

variable {β : Type*} [SigmaAlgebra β]

lemma _root_.Measurable.eval_matrix {i : m} {j : n} {M : β → Matrix m n α} (hM : Measurable M) :
    Measurable (M · i j) := hM.eval.eval

lemma _root_.Measurable.of_eval_matrix (M : β → Matrix m n α)
    (hM : ∀ i j, Measurable (M · i j)) : Measurable M :=
  .of_eval (fun i ↦ .of_eval fun j ↦ hM i j)

protected lemma measurable_iff {M : β → Matrix m n α} :
    Measurable M ↔ ∀ i j, Measurable (M · i j) where
  mp h _ _ := h.eval_matrix
  mpr h := Measurable.of_eval_matrix M h

protected lemma measurable_apply {i : m} {j : n} :
    Measurable (fun M : Matrix m n α ↦ M i j) := measurable_id.eval_matrix

end SigmaAlgebra

section MeasurableEquiv

variable (m n α : Type*) [SigmaAlgebra α]

@[fun_prop]
lemma measurable_of : Measurable <| Matrix.of (m := m) (n := n) (α := α) :=
  measurable_id

instance [Countable m] [Countable n] [TopologicalSpace α] [SecondCountableTopology α]
  [BorelSpace α] : BorelSpace (Matrix m n α) := inferInstanceAs <| BorelSpace (m → n → α)

/-- The map from `m → n → α` to `Matrix m n α` as a measurable equivalence. -/
protected def ofMeasurableEquiv : (m → n → α) ≃ᵐ (Matrix m n α) where
  toEquiv := Matrix.of
  measurable_toFun := measurable_id
  measurable_invFun := measurable_of m n α

lemma coe_ofMeasurableEquiv : ⇑(Matrix.ofMeasurableEquiv m n α) = Matrix.of := rfl

lemma coe_ofMeasurableEquiv_symm : ⇑(Matrix.ofMeasurableEquiv m n α).symm = Matrix.of.symm := rfl

@[simp]
lemma ofMeasurableEquiv_apply (f : m → n → α) :
    Matrix.ofMeasurableEquiv m n α f = Matrix.of f := rfl

@[simp]
lemma ofMeasurableEquiv_symm_apply (M : Matrix m n α) :
    (Matrix.ofMeasurableEquiv m n α).symm M = Matrix.of.symm M := rfl

end MeasurableEquiv

end Matrix
