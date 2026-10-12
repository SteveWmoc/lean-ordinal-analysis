import Mathlib.Order.Hom.Basic
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Generic verified ordinal notation systems

This file extracts the small semantic interface shared by concrete recursive
ordinal notation systems.

The abstraction deliberately begins at the canonical notation type. It does
not prescribe raw syntax, normal forms, normalization algorithms, arithmetic,
or any particular implementation of executable comparison. Those choices are
expected to vary substantially between ε₀, Γ₀, and later collapsing systems.
-/

namespace OrdinalAnalysis

universe u

/--
A canonical ordinal notation system certified as an exact initial segment of
the ordinals below `bound`.

The concrete notation type supplies its own linear order. The structure
records only the semantic map and the two directions needed to certify that
the notation order agrees with ordinal order and covers every ordinal below
the stated bound.
-/
structure OrdinalNotationSystem (N : Type u) [LinearOrder N] where
  /-- Semantic interpretation of canonical notations. -/
  eval : N → Ordinal.{0}
  /-- The first ordinal not represented by the notation system. -/
  bound : Ordinal.{0}
  /-- Every canonical notation evaluates strictly below `bound`. -/
  eval_lt_bound : ∀ a, eval a < bound
  /-- Syntactic strict order agrees exactly with semantic ordinal order. -/
  lt_iff_eval_lt : ∀ a b, a < b ↔ eval a < eval b
  /-- Every ordinal below `bound` has a canonical representative. -/
  complete : ∀ {α : Ordinal.{0}}, α < bound → ∃ a, eval a = α

namespace OrdinalNotationSystem

variable {N : Type u} [LinearOrder N]

/-- Semantic evaluation is strictly monotone. -/
theorem eval_strictMono (system : OrdinalNotationSystem N) :
    StrictMono system.eval := by
  intro a b hab
  exact (system.lt_iff_eval_lt a b).1 hab

/-- Semantic evaluation is monotone. -/
theorem eval_monotone (system : OrdinalNotationSystem N) :
    Monotone system.eval :=
  system.eval_strictMono.monotone

/-- Semantic evaluation is injective. -/
theorem eval_injective (system : OrdinalNotationSystem N) :
    Function.Injective system.eval :=
  system.eval_strictMono.injective

/-- Package semantic evaluation as an order embedding into `Ordinal`. -/
noncomputable def evalOrderEmbedding
    (system : OrdinalNotationSystem N) : N ↪o Ordinal.{0} :=
  OrderEmbedding.ofStrictMono system.eval system.eval_strictMono

@[simp]
theorem evalOrderEmbedding_apply
    (system : OrdinalNotationSystem N) (a : N) :
    system.evalOrderEmbedding a = system.eval a :=
  rfl

/-- Semantic strict comparison reflects exactly the notation order. -/
@[simp]
theorem eval_lt_eval_iff
    (system : OrdinalNotationSystem N) (a b : N) :
    system.eval a < system.eval b ↔ a < b :=
  (system.lt_iff_eval_lt a b).symm

/-- Non-strict notation order agrees with semantic ordinal order. -/
theorem le_iff_eval_le
    (system : OrdinalNotationSystem N) (a b : N) :
    a ≤ b ↔ system.eval a ≤ system.eval b := by
  constructor
  · intro hab
    exact system.eval_monotone hab
  · intro hab
    by_contra hnot
    have hba : b < a := lt_of_not_ge hnot
    have heval : system.eval b < system.eval a :=
      system.eval_strictMono hba
    exact (not_lt_of_ge hab) heval

/-- Semantic non-strict comparison reflects exactly the notation order. -/
@[simp]
theorem eval_le_eval_iff
    (system : OrdinalNotationSystem N) (a b : N) :
    system.eval a ≤ system.eval b ↔ a ≤ b :=
  (system.le_iff_eval_le a b).symm

end OrdinalNotationSystem
end OrdinalAnalysis
