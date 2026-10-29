import OrdinalAnalysis.Gamma0.ExactInitialSegment

/-!
# Γ₀ examples for the generic notation-system API

These examples check the adapter, generic order and range theorems, and
compatibility of the resulting order isomorphism with the concrete Γ₀ API.
The classifier interface is separate and is not asserted here.
-/

namespace OrdinalAnalysis
namespace G0

open Ordinal

example : notationSystem.bound = (Γ₀ : Ordinal.{0}) :=
  rfl

example (a b : G0) :
    a < b ↔ notationSystem.eval a < notationSystem.eval b :=
  notationSystem.lt_iff_eval_lt a b

example (a b : G0) :
    notationSystem.eval a ≤ notationSystem.eval b ↔ a ≤ b :=
  notationSystem.eval_le_eval_iff a b

example :
    Set.range notationSystem.eval = Set.Iio (Γ₀ : Ordinal.{0}) := by
  simpa only [notationSystem_bound] using notationSystem.range_eval_eq_Iio

noncomputable example : G0 ≃o Set.Iio (Γ₀ : Ordinal.{0}) :=
  orderIsoIioGammaZero

example (a : G0) :
    orderIsoIioGammaZero a = evalOrderEmbeddingIio a :=
  orderIsoIioGammaZero_apply a

example (o : Set.Iio (Γ₀ : Ordinal.{0})) :
    orderIsoIioGammaZero.symm o = ofOrdinal o.1 o.2 := by
  simp

example (a : G0) :
    orderIsoIioGammaZero.symm (orderIsoIioGammaZero a) = a :=
  orderIsoIioGammaZero.symm_apply_apply a

example (o : Set.Iio (Γ₀ : Ordinal.{0})) :
    orderIsoIioGammaZero (ofOrdinal o.1 o.2) = o := by
  apply Subtype.ext
  exact eval_ofOrdinal o.1 o.2

example :
    orderIsoIioGammaZero.symm
      ⟨(ε₀ : Ordinal.{0}), Ordinal.epsilon_zero_lt_gamma 0⟩ = epsilonZero := by
  apply eval_injective
  exact (congrArg Subtype.val
    (orderIsoIioGammaZero.apply_symm_apply
      ⟨(ε₀ : Ordinal.{0}), Ordinal.epsilon_zero_lt_gamma 0⟩)).trans
    eval_epsilonZero.symm

end G0
end OrdinalAnalysis
