/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.Order.GeneralizedBooleanAlgebra.Cofinality

/-!
# Countable separation and cofinality of Boolean algebras

`BooleanAlgebra.CountableSeparationProperty` says that two countable, crosswise disjoint
families can be separated by an element and its complement. Koppelberg calls this property
*almost sigma-completeness*. It is equivalent to the generalized Boolean separation property.

`BooleanSubalgebra.HasCountableCofinality` means that a Boolean algebra is the union of a
strictly increasing sequence of Boolean subalgebras. This concerns exhaustion by proper
subalgebras, not order cofinality in the Boolean algebra (which already has a greatest element).

The main result is that countable separation prevents such an exhaustion. More generally,
every monotone sequence of subalgebras exhausting the algebra reaches the top subalgebra.
These results specialize the common generalized Boolean algebra theorem.

## References

* [Sabine Koppelberg, *Boolean algebras as unions of chains of subalgebras*][Koppelberg1977],
  Theorem 1, pp. 196–198.
-/

@[expose] public section

open Set

variable {B : Type*}

namespace BooleanAlgebra

variable [BooleanAlgebra B]

variable (B) in
/-- The countable separation property of a Boolean algebra: any two countable families
whose members are crosswise disjoint have a separator. Koppelberg calls this property
*almost sigma-completeness*. -/
def CountableSeparationProperty : Prop :=
  ∀ ⦃M N : Set B⦄, M.Countable → N.Countable →
    (∀ m ∈ M, ∀ n ∈ N, Disjoint m n) →
    ∃ b : B, (∀ m ∈ M, m ≤ b) ∧ ∀ n ∈ N, n ≤ bᶜ

/-- Koppelberg's complement formulation is the generalized Boolean countable separation
property specialized to a Boolean algebra. -/
theorem countableSeparationProperty_iff :
    CountableSeparationProperty B ↔
      GeneralizedBooleanAlgebra.CountableSeparationProperty B := by
  simp only [CountableSeparationProperty,
    GeneralizedBooleanAlgebra.CountableSeparationProperty, le_compl_iff_disjoint_left]

/-- A Boolean algebra in which every countable set has a supremum has the countable
separation property. This isolates the exact completeness input used to obtain Koppelberg's
hypothesis; no arbitrary suprema are required. -/
theorem countableSeparationProperty_of_countable_isLUB
    (hcomplete : ∀ S : Set B, S.Countable → ∃ s, IsLUB S s) :
    CountableSeparationProperty B :=
  countableSeparationProperty_iff.mpr
    (GeneralizedBooleanAlgebra.countableSeparationProperty_of_countable_isLUB hcomplete)

end BooleanAlgebra

namespace CompleteBooleanAlgebra

/-- Every complete Boolean algebra has the countable separation property. -/
theorem countableSeparationProperty (B : Type*) [CompleteBooleanAlgebra B] :
    BooleanAlgebra.CountableSeparationProperty B :=
  BooleanAlgebra.countableSeparationProperty_of_countable_isLUB fun S _ ↦
    ⟨sSup S, isLUB_sSup S⟩

end CompleteBooleanAlgebra

namespace BooleanSubalgebra

variable [BooleanAlgebra B]

variable (B) in
/-- A Boolean algebra has countable cofinality by subalgebras if a strictly increasing
sequence of Boolean subalgebras exhausts it. Strict increase implies that every stage is
proper. This is distinct from order cofinality in the underlying Boolean algebra. -/
def HasCountableCofinality : Prop :=
  ∃ C : ℕ → BooleanSubalgebra B, StrictMono C ∧ ∀ b, ∃ n, b ∈ C n

/-- Countable separation forces every monotone exhaustive sequence of Boolean subalgebras
to reach the whole algebra. This is the obstruction proved in Koppelberg's Theorem 1. -/
theorem exists_eq_top_of_countableSeparationProperty
    (hsep : BooleanAlgebra.CountableSeparationProperty B)
    (C : ℕ → BooleanSubalgebra B) (hC : Monotone C) (hcover : ∀ b, ∃ n, b ∈ C n) :
    ∃ n, C n = ⊤ := by
  obtain ⟨n, hn⟩ := GeneralizedBooleanSubalgebra.exists_eq_top_of_countableSeparationProperty
    (BooleanAlgebra.countableSeparationProperty_iff.mp hsep)
    (fun n ↦ (C n).toGeneralizedBooleanSubalgebra) (fun i j hij ↦ hC hij) hcover
  refine ⟨n, top_unique fun b _ ↦ ?_⟩
  change b ∈ (C n).toGeneralizedBooleanSubalgebra
  rw [hn]
  exact GeneralizedBooleanSubalgebra.mem_top

/-- A monotone exhaustive sequence in a Boolean algebra with countable separation
is eventually the constant sequence of top subalgebras. -/
theorem exists_forall_eq_top_of_countableSeparationProperty
    (hsep : BooleanAlgebra.CountableSeparationProperty B)
    (C : ℕ → BooleanSubalgebra B) (hC : Monotone C) (hcover : ∀ b, ∃ n, b ∈ C n) :
    ∃ n, ∀ m, n ≤ m → C m = ⊤ := by
  obtain ⟨n, hn⟩ := exists_eq_top_of_countableSeparationProperty hsep C hC hcover
  exact ⟨n, fun m hnm ↦ top_unique (hn ▸ hC hnm)⟩

/-- A Boolean algebra with countable separation has no strictly increasing countable
exhaustion by Boolean subalgebras (Koppelberg, Theorem 1). -/
theorem not_hasCountableCofinality_of_countableSeparationProperty
    (hsep : BooleanAlgebra.CountableSeparationProperty B) : ¬ HasCountableCofinality B := by
  rintro ⟨C, hC, hcover⟩
  obtain ⟨n, hn⟩ := exists_eq_top_of_countableSeparationProperty hsep C hC.monotone hcover
  exact (hC (Nat.lt_succ_self n)).not_ge (hn ▸ le_top)

end BooleanSubalgebra
