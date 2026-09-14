import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo

/-!
# Strict parabolic eigenvalues

These tests ensure that `Matrix.parabolicEigenvalue` and its general-linear-group facade require
parabolicity, while routine uses remain proof-irrelevant and simplify to the total `halfTrace`
expression.
-/

open Matrix

set_option linter.unusedVariables false in
example (m : Matrix (Fin 2) (Fin 2) ℚ) : True := by
  fail_if_success
    let _a : ℚ := m.parabolicEigenvalue
  trivial

set_option linter.unusedVariables false in
example (m : Matrix (Fin 2) (Fin 2) ℚ) : True := by
  fail_if_success
    let _a : ℚ := (fun _ : ℚ => 0) m.parabolicEigenvalue
  trivial

example (m : Matrix (Fin 2) (Fin 2) ℚ) : ℚ := m.halfTrace

example (m : Matrix (Fin 2) (Fin 2) ℚ) (hm : m.IsParabolic) : ℚ :=
  m.parabolicEigenvalue hm

example (g : GL (Fin 2) ℚ) (hg : g.IsParabolic) : ℚ :=
  g.parabolicEigenvalue hg

set_option linter.unusedVariables false in
example (g : GL (Fin 2) ℚ) : True := by
  fail_if_success
    let _a : ℚ := g.parabolicEigenvalue
  trivial

example (g : GL (Fin 2) ℚ) (hg : g.IsParabolic) :
    g.parabolicEigenvalue hg = g.halfTrace := by
  simp

example (m : Matrix (Fin 2) (Fin 2) ℚ) (hm₁ hm₂ : m.IsParabolic) :
    m.parabolicEigenvalue hm₁ = m.parabolicEigenvalue hm₂ := rfl

example (m : Matrix (Fin 2) (Fin 2) ℚ) (hm : m.IsParabolic) :
    m.parabolicEigenvalue hm = m.halfTrace := by
  simp

variable {K : Type*} [Field K]

set_option linter.unusedVariables false in
example (m : Matrix (Fin 2) (Fin 2) K) (hm : m.IsParabolic) : True := by
  fail_if_success
    let _a : K := m.parabolicEigenvalue hm
  trivial

example (m : Matrix (Fin 2) (Fin 2) K) : K := m.halfTrace

variable {L : Type*} [Field L] [CharZero L]

example (m : Matrix (Fin 2) (Fin 2) L) (hm : m.IsParabolic) : L :=
  m.parabolicEigenvalue hm

example (g : GL (Fin 2) L) (hg : g.IsParabolic) : L :=
  g.parabolicEigenvalue hg
