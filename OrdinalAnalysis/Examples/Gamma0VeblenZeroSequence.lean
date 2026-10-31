import OrdinalAnalysis.Gamma0.VeblenZeroSequence
import OrdinalAnalysis.Gamma0.FiniteBlocks

/-!
# Executable first-fixed-point sequences at successor Veblen indices
-/

namespace OrdinalAnalysis
namespace Examples

open Ordinal

-- The tower 0, 1, ω, ω^ω, ... approaches ε₀.
example : G0.veblenZeroSequence G0.zero 0 = G0.zero := by native_decide
example : G0.veblenZeroSequence G0.zero 1 = G0.one := by native_decide
example : G0.veblenZeroSequence G0.zero 2 = G0.omega := by native_decide
example : G0.veblenZeroSequence G0.zero 3 = G0.veblen G0.zero G0.omega := by
  native_decide

-- Iterating φ₁ starts at 0, ε₀, φ₁(ε₀), ... and approaches φ₂(0).
example : G0.veblenZeroSequence G0.one 1 = G0.epsilonZero := by native_decide
example : G0.veblenZeroSequence G0.one 2 =
    G0.veblen G0.one G0.epsilonZero := by native_decide
example : G0.veblenZeroSequence G0.one 2 < G0.veblen (G0.ofNat 2) G0.zero := by
  native_decide

example :
    (⨆ n, G0.eval (G0.veblenZeroSequence G0.zero n)) = (ε₀ : Ordinal.{0}) := by
  have h := G0.veblenZeroSequence_iSup_eval
    (index := G0.one) (lower := G0.zero) (by native_decide)
  simpa only [G0.eval_veblen, G0.eval_one, G0.eval_zero] using h

example :
    (⨆ n, G0.eval (G0.veblenZeroSequence G0.one n)) =
      Ordinal.veblen 2 0 := by
  have h := G0.veblenZeroSequence_iSup_eval
    (index := G0.ofNat 2) (lower := G0.one) (by native_decide)
  simpa only [G0.eval_veblen, G0.eval_ofNat, G0.eval_zero, Nat.cast_ofNat] using h

example (index lower : G0) (hpred : G0.predecessor? index = some lower) :
    (ClassificationResult.limit (G0.veblenZeroSequence lower)).Satisfies
      G0.notationSystem (G0.veblen index G0.zero) :=
  (G0.veblenZeroLimitSequenceData hpred).satisfies

end Examples
end OrdinalAnalysis
