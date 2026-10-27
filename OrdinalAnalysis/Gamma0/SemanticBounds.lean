import OrdinalAnalysis.Gamma0.Semantics
import Mathlib.SetTheory.Ordinal.Principal

/-!
# Semantic upper bounds for Γ₀ syntax

Every finite raw term evaluates below the Feferman–Schütte ordinal. Normality
is unnecessary for this upper bound: it is needed for uniqueness and comparison
correctness, rather than for closure of the semantic operations.

The proof uses closure below Γ₀ under Veblen application, finite right
multiplication, and addition.
-/

namespace OrdinalAnalysis

open Ordinal

namespace Gamma0Bounds

/-- Veblen application preserves the initial segment below Γ₀. -/
theorem veblen_lt_gamma_zero {a b : Ordinal.{0}}
    (ha : a < Γ₀) (hb : b < Γ₀) :
    Ordinal.veblen a b < Γ₀ := by
  have hfixed : Ordinal.veblen a Γ₀ = Γ₀ := by
    have h := Ordinal.veblen_veblen_of_lt ha 0
    simpa only [Ordinal.veblen_gamma_zero] using h
  exact (Ordinal.veblen_right_strictMono a hb).trans_eq hfixed

/-- Γ₀ is additively indecomposable. -/
theorem isPrincipal_add_gamma_zero :
    Ordinal.IsPrincipal (· + ·) (Γ₀ : Ordinal.{0}) := by
  apply Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.2
  right
  simpa only [Ordinal.veblen_gamma_zero] using
    Ordinal.veblen_mem_range_opow (Γ₀ : Ordinal.{0}) 0

/-- Finite sums of ordinals below Γ₀ remain below Γ₀. -/
theorem add_lt_gamma_zero {a b : Ordinal.{0}}
    (ha : a < Γ₀) (hb : b < Γ₀) : a + b < Γ₀ :=
  isPrincipal_add_gamma_zero ha hb

/-- Multiplication on the right by a natural coefficient preserves the Γ₀ bound. -/
theorem mul_natCast_lt_gamma_zero {a : Ordinal.{0}}
    (ha : a < Γ₀) (n : Nat) : a * (n : Ordinal.{0}) < Γ₀ :=
  isPrincipal_add_gamma_zero.mul_natCast_lt ha n

end Gamma0Bounds

namespace G0Term

/-- Every raw finite Γ₀ term evaluates below Γ₀, including noncanonical terms. -/
theorem eval_lt_gamma_zero (t : G0Term) :
    eval t < Γ₀ := by
  induction t with
  | zero =>
      exact Ordinal.gamma_pos
  | veblen index arg coeff tail ihIndex ihArg ihTail =>
      rw [eval_veblen]
      exact Gamma0Bounds.add_lt_gamma_zero
        (Gamma0Bounds.mul_natCast_lt_gamma_zero
          (Gamma0Bounds.veblen_lt_gamma_zero ihIndex ihArg) coeff.succ)
        ihTail

end G0Term

namespace G0

/-- Every canonical Γ₀ notation evaluates below Γ₀. -/
theorem eval_lt_gamma_zero (a : G0) :
    eval a < Γ₀ :=
  G0Term.eval_lt_gamma_zero a.1

/-- Soundness: the semantic range is contained in the initial segment below Γ₀. -/
theorem range_eval_subset_Iio_gamma_zero :
    Set.range eval ⊆ Set.Iio (Γ₀ : Ordinal.{0}) := by
  rintro _ ⟨a, rfl⟩
  exact eval_lt_gamma_zero a

end G0
end OrdinalAnalysis
