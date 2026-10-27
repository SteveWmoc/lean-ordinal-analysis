import OrdinalAnalysis.Gamma0.BoundedEmbedding

/-!
# Examples of Γ₀ semantic soundness

The upper bound applies to arbitrary raw terms, including the intentionally
noncanonical examples. Canonical terms also have a bounded order embedding.
-/

namespace OrdinalAnalysis

open Ordinal

example (t : G0Term) : G0Term.eval t < Γ₀ :=
  G0Term.eval_lt_gamma_zero t

example : G0Term.eval G0Term.badFixedPoint < Γ₀ :=
  G0Term.eval_lt_gamma_zero _

example : G0Term.eval G0Term.badAscending < Γ₀ :=
  G0Term.eval_lt_gamma_zero _

example (a : G0) : (G0.evalOrderEmbeddingIio a).1 < Γ₀ :=
  (G0.evalOrderEmbeddingIio a).2

example (a : G0) :
    (G0.evalOrderEmbeddingIio a : Ordinal.{0}) = G0.evalOrderEmbedding a := by
  simp

example (a b : G0) :
    G0.evalOrderEmbeddingIio a < G0.evalOrderEmbeddingIio b ↔ a < b := by
  simp

example : G0.eval G0.epsilonZero < Γ₀ :=
  G0.eval_lt_gamma_zero _

end OrdinalAnalysis
