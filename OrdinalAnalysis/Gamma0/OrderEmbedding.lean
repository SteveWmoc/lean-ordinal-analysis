import OrdinalAnalysis.Gamma0.LinearOrder
import Mathlib.Order.Hom.Basic

/-!
# Ordinal embedding of canonical Γ₀ notations

Semantic correctness and the linear-order structure on `G0` allow us to
package ordinal evaluation as a genuine order embedding into mathlib's
`Ordinal`.

This is the interface later range and completeness theorems should use.
-/

namespace OrdinalAnalysis
namespace G0

/-- Evaluation of canonical Γ₀ terms is strictly monotone. -/
theorem eval_strictMono : StrictMono eval := by
  intro a b hab
  exact (lt_iff_eval_lt a b).1 hab

/-- Evaluation of canonical Γ₀ terms is monotone. -/
theorem eval_monotone : Monotone eval :=
  eval_strictMono.monotone

/-- Canonical Γ₀ notation embeds order-reflectingly into mathlib ordinals. -/
noncomputable def evalOrderEmbedding : G0 ↪o Ordinal.{0} :=
  OrderEmbedding.ofStrictMono eval eval_strictMono

@[simp]
theorem evalOrderEmbedding_apply (a : G0) :
    evalOrderEmbedding a = eval a :=
  rfl

/-- Semantic strict comparison reflects exactly the canonical syntax order. -/
@[simp]
theorem eval_lt_eval_iff (a b : G0) :
    eval a < eval b ↔ a < b :=
  (lt_iff_eval_lt a b).symm

/-- Semantic non-strict comparison reflects exactly the canonical syntax order. -/
@[simp]
theorem eval_le_eval_iff (a b : G0) :
    eval a ≤ eval b ↔ a ≤ b :=
  (le_iff_eval_le a b).symm

end G0
end OrdinalAnalysis
