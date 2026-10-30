import OrdinalAnalysis.Gamma0.OmegaMultipleSequence
import OrdinalAnalysis.Gamma0.Predecessor

/-!
# Executable examples of the first Γ₀ limit sequences
-/

namespace OrdinalAnalysis
namespace Examples

open Ordinal

example : G0.ofNat 0 = G0.zero := by native_decide
example : G0.ofNat 1 = G0.one := by native_decide
example : G0.omegaMultiple 1 = G0.omega := by native_decide

-- The sequence at ω is 0, 1, 2, ...
example : G0.omegaMultipleSequence 0 4 = G0.ofNat 4 := by native_decide
-- The sequence at ω · 2 starts at ω.
example : G0.omegaMultipleSequence 1 0 = G0.omega := by native_decide
example : G0.predecessor? (G0.omegaMultipleSequence 1 1) = some G0.omega := by
  native_decide

-- Exercise larger finite blocks through the executable order.
example : G0.omegaMultipleSequence 2 5 < G0.omegaMultipleSequence 2 6 := by
  native_decide
example : G0.omegaMultipleSequence 2 100 < G0.omegaMultiple 3 := by
  native_decide

example (k : Nat) :
    (⨆ n, G0.eval (G0.omegaMultipleSequence k n)) =
      G0.eval (G0.omegaMultiple k.succ) :=
  G0.omegaMultipleSequence_iSup_eval k

example (k : Nat) :
    (ClassificationResult.limit (G0.omegaMultipleSequence k)).Satisfies
      G0.notationSystem (G0.omegaMultiple k.succ) :=
  G0.omegaMultipleSequence_satisfies k

end Examples
end OrdinalAnalysis
