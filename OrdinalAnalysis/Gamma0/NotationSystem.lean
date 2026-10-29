import OrdinalAnalysis.Generic.OrdinalNotationSystem
import OrdinalAnalysis.Gamma0.Completeness

/-!
# Γ₀ as a generic ordinal notation system

The verified order, soundness, and completeness of canonical Veblen notations
satisfy the existing generic interface without changing the generic layer or
the concrete computational definitions.
-/

namespace OrdinalAnalysis
namespace G0

open Ordinal

/-- Canonical Veblen notations form an exact notation system below Γ₀. -/
noncomputable def notationSystem : OrdinalNotationSystem G0 where
  eval := eval
  bound := Γ₀
  eval_lt_bound := eval_lt_gamma_zero
  lt_iff_eval_lt := lt_iff_eval_lt
  complete := fun {o} hbound => exists_eval_eq o hbound

@[simp]
theorem notationSystem_eval (a : G0) :
    notationSystem.eval a = eval a :=
  rfl

@[simp]
theorem notationSystem_bound :
    notationSystem.bound = (Γ₀ : Ordinal.{0}) :=
  rfl

end G0
end OrdinalAnalysis
