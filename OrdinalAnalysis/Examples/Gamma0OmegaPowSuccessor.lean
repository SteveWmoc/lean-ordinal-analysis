import OrdinalAnalysis.Gamma0.OmegaPowSuccessorSequence
import OrdinalAnalysis.Gamma0.FiniteBlocks

/-!
# Native examples for finite principal multiples and successor-exponent sequences
-/

namespace OrdinalAnalysis
namespace Examples

open Ordinal

private def epsilonPlusOne : G0 :=
  ⟨.veblen G0Term.one .zero 0 G0Term.one, by native_decide⟩

private def epsilonTwice : G0 :=
  ⟨.veblen G0Term.one .zero 1 .zero, by native_decide⟩

example : G0.veblenMulNat G0.zero G0.zero 0 = G0.zero := by native_decide
example : G0.veblenMulNat G0.zero G0.zero 5 = G0.ofNat 5 := by native_decide
example : G0.veblenMulNat G0.zero G0.one 3 = G0.omegaMultiple 3 := by native_decide

-- A fixed-point collapse still scales the correct canonical principal term.
example : G0.veblenMulNat G0.zero G0.epsilonZero 2 = epsilonTwice := by
  native_decide

example : G0.omegaPowSuccSequence G0.zero 4 = G0.ofNat 4 := by native_decide
example : G0.omegaPowSuccSequence G0.one 4 = G0.omegaMultiple 4 := by native_decide
example : G0.omegaPowSuccSequence G0.epsilonZero 2 = epsilonTwice := by native_decide

example : G0.predecessor? epsilonPlusOne = some G0.epsilonZero := by native_decide

example :
    (⨆ n, G0.eval (G0.omegaPowSuccSequence G0.one n)) =
      ω ^ G0.eval (G0.ofNat 2) := by
  apply G0.omegaPowSuccSequence_iSup_eval
  native_decide

example :
    (⨆ n, G0.eval (G0.omegaPowSuccSequence G0.epsilonZero n)) =
      ω ^ G0.eval epsilonPlusOne := by
  apply G0.omegaPowSuccSequence_iSup_eval
  native_decide

example (a b : G0) (hpred : G0.predecessor? a = some b) :
    (ClassificationResult.limit (G0.omegaPowSuccSequence b)).Satisfies
      G0.notationSystem (G0.veblen G0.zero a) :=
  (G0.omegaPowSuccLimitSequenceData hpred).satisfies

end Examples
end OrdinalAnalysis
