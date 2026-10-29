import OrdinalAnalysis.Generic.ExactInitialSegment
import OrdinalAnalysis.Gamma0.NotationSystem

/-!
# The exact Γ₀ ordinal initial segment

The generic initial-segment construction packages evaluation as an order
isomorphism. Compatibility lemmas identify its maps with the existing bounded
embedding and the chosen semantic inverse.
-/

namespace OrdinalAnalysis
namespace G0

open Ordinal

/-- Canonical Γ₀ notations are order-isomorphic to all ordinals below Γ₀. -/
noncomputable def orderIsoIioGammaZero :
    G0 ≃o Set.Iio (Γ₀ : Ordinal.{0}) :=
  notationSystem.orderIsoIio

/-- The forward isomorphism evaluates the notation. -/
@[simp]
theorem orderIsoIioGammaZero_apply_coe (a : G0) :
    (orderIsoIioGammaZero a : Ordinal.{0}) = eval a :=
  rfl

/-- The isomorphism's forward map is the existing bounded embedding. -/
theorem orderIsoIioGammaZero_apply (a : G0) :
    orderIsoIioGammaZero a = evalOrderEmbeddingIio a := by
  apply Subtype.ext
  rfl

/-- The generic inverse agrees with the canonical representative chosen by completeness. -/
@[simp]
theorem orderIsoIioGammaZero_symm_apply (o : Set.Iio (Γ₀ : Ordinal.{0})) :
    orderIsoIioGammaZero.symm o = ofOrdinal o.1 o.2 := by
  apply eval_injective
  calc
    eval (orderIsoIioGammaZero.symm o) = o.1 :=
      congrArg Subtype.val (orderIsoIioGammaZero.apply_symm_apply o)
    _ = eval (ofOrdinal o.1 o.2) := (eval_ofOrdinal o.1 o.2).symm

end G0
end OrdinalAnalysis
