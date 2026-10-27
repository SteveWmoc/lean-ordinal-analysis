import OrdinalAnalysis.Gamma0.VeblenDecomposition

/-!
# Examples of the decreasing semantic decomposition

The reconstruction identity matches the raw Veblen constructor. The recursive
inputs satisfy the strict bounds needed for the later completeness proof.
-/

namespace OrdinalAnalysis

open Ordinal Gamma0Decomposition

example (o : Ordinal.{0}) (hne : o ≠ 0) (hbound : o < Γ₀) :
    let d := decompose o hne hbound
    Ordinal.veblen d.index d.arg * (d.coeff.succ : Ordinal.{0}) + d.tail = o :=
  (decompose o hne hbound).eval_eq

example (o : Ordinal.{0}) (hne : o ≠ 0) (hbound : o < Γ₀) :
    let d := decompose o hne hbound
    d.index < Γ₀ ∧ d.arg < Γ₀ ∧ d.tail < Γ₀ := by
  dsimp only
  exact ⟨(decompose o hne hbound).index_lt.trans hbound,
    (decompose o hne hbound).arg_lt.trans hbound,
    (decompose o hne hbound).tail_lt.trans hbound⟩

-- ε₀ is a fixed point of exponentiation, but the inverse Veblen index still decreases.
example : Ordinal.invVeblen₁ (ε₀ : Ordinal.{0}) < ε₀ :=
  invVeblen₁_lt_of_pos_lt_gamma_zero
    (Ordinal.epsilon_pos 0) (Ordinal.epsilon_zero_lt_gamma 0)

-- The strict inverse-index bound cannot extend to Γ₀ itself.
example : Ordinal.invVeblen₁ (Γ₀ : Ordinal.{0}) = Γ₀ :=
  Ordinal.invVeblen₁_gamma 0

end OrdinalAnalysis
