import OrdinalAnalysis.Gamma0.OrderEmbedding
import OrdinalAnalysis.Gamma0.SemanticBounds

/-!
# Evaluation into the initial segment below Γ₀

Semantic soundness restricts the ordinal evaluation embedding to `Set.Iio Γ₀`.
Surjectivity onto that initial segment is a separate completeness theorem.
-/

namespace OrdinalAnalysis
namespace G0

open Ordinal

/-- Canonical Γ₀ notations embed into the ordinals strictly below Γ₀. -/
noncomputable def evalOrderEmbeddingIio :
    G0 ↪o Set.Iio (Γ₀ : Ordinal.{0}) where
  toFun a := ⟨eval a, eval_lt_gamma_zero a⟩
  inj' := by
    intro a b hab
    apply eval_injective
    exact congrArg Subtype.val hab
  map_rel_iff' := by
    intro a b
    exact (le_iff_eval_le a b).symm

/-- Forgetting the Γ₀ bound recovers the original ordinal evaluation. -/
@[simp]
theorem coe_evalOrderEmbeddingIio_apply (a : G0) :
    (evalOrderEmbeddingIio a : Ordinal.{0}) = eval a :=
  rfl

/-- The bounded embedding has exactly the original evaluation as its value. -/
@[simp]
theorem evalOrderEmbeddingIio_apply_lt_apply_iff (a b : G0) :
    evalOrderEmbeddingIio a < evalOrderEmbeddingIio b ↔ a < b := by
  change eval a < eval b ↔ a < b
  exact eval_lt_eval_iff a b

end G0
end OrdinalAnalysis
