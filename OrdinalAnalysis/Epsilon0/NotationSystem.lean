import OrdinalAnalysis.Generic.OrdinalNotationSystem
import OrdinalAnalysis.Epsilon0.LimitFundamentalSequence

/-!
# The ε₀ notation system as a generic ordinal notation system

This file packages the completed ε₀ development as an instance of the generic
`OrdinalNotationSystem` interface. No ε₀ implementation is changed or
redefined here; this is a one-way adapter over the verified public API.
-/

namespace OrdinalAnalysis
namespace E0

open Ordinal

/--
The canonical ε₀ notation type, certified as an exact notation system for the
ordinals below `ε₀`.
-/
noncomputable def notationSystem : OrdinalNotationSystem E0 where
  eval := eval
  bound := ε₀
  eval_lt_bound := eval_lt_epsilon_zero
  lt_iff_eval_lt := lt_iff_eval_lt
  complete := exists_eval_eq_of_lt_epsilon_zero

@[simp]
theorem notationSystem_eval (a : E0) :
    notationSystem.eval a = eval a :=
  rfl

@[simp]
theorem notationSystem_bound :
    notationSystem.bound = ε₀ :=
  rfl

end E0
end OrdinalAnalysis
