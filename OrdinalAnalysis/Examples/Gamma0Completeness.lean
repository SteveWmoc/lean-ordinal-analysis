import OrdinalAnalysis.Gamma0.Completeness

/-!
# Examples of Γ₀ completeness

The exact range theorem covers every ordinal below Γ₀. The inverse round trips
also check that the chosen semantic construction respects canonical syntax.
-/

namespace OrdinalAnalysis

open Ordinal

example (o : Ordinal.{0}) (hbound : o < Γ₀) :
    ∃ a : G0, G0.eval a = o :=
  G0.exists_eval_eq o hbound

example (o : Ordinal.{0}) :
    o ∈ Set.range G0.eval ↔ o < Γ₀ := by
  rw [G0.range_eval_eq_Iio_gamma_zero]
  rfl

example (a : G0) :
    G0.ofOrdinal (G0.eval a) (G0.eval_lt_gamma_zero a) = a := by
  simp

example (o : Set.Iio (Γ₀ : Ordinal.{0})) :
    G0.evalOrderEmbeddingIio (G0.ofOrdinal o.1 o.2) = o := by
  apply Subtype.ext
  exact G0.eval_ofOrdinal o.1 o.2

example : Γ₀ ∉ Set.range G0.eval := by
  rw [G0.range_eval_eq_Iio_gamma_zero]
  exact lt_irrefl (Γ₀ : Ordinal.{0})

example : G0.ofOrdinal (ε₀ : Ordinal.{0}) (Ordinal.epsilon_zero_lt_gamma 0) =
    G0.epsilonZero := by
  apply G0.eval_injective
  simp

end OrdinalAnalysis
