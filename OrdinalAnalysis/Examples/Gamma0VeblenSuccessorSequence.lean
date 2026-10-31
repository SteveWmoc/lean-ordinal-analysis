import OrdinalAnalysis.Gamma0.VeblenSuccessorSequence
import OrdinalAnalysis.Gamma0.FiniteBlocks

/-!
# Executable successors and next-fixed-point sequences
-/

namespace OrdinalAnalysis
namespace Examples

open Ordinal

example : G0.successor G0.zero = G0.one := by native_decide
example : G0.successor (G0.ofNat 7) = G0.ofNat 8 := by native_decide
example : G0.successor G0.omega = G0.omegaMulAddNat 1 1 := by native_decide
example : G0.successor (G0.omegaMulAddNat 2 3) =
    G0.omegaMulAddNat 2 4 := by native_decide
example : G0.predecessor? (G0.successor G0.epsilonZero) =
    some G0.epsilonZero := by native_decide
example : G0.successor (G0.veblen G0.zero G0.epsilonZero) =
    G0.successor G0.epsilonZero := by native_decide

-- ε₀ + 1, ω^(ε₀ + 1), ω^(ω^(ε₀ + 1)), ... approach ε₁.
example : G0.veblenSuccSequence G0.zero G0.one G0.zero 0 =
    G0.successor G0.epsilonZero := by native_decide
example : G0.veblenSuccSequence G0.zero G0.one G0.zero 1 =
    G0.veblen G0.zero (G0.successor G0.epsilonZero) := by native_decide
example : G0.veblenSuccSequence G0.zero G0.one G0.zero 2 <
    G0.veblen G0.one G0.one := by native_decide

-- The same construction works above the first φ₁-fixed point.
example : G0.veblenSuccSequence G0.one (G0.ofNat 2) G0.zero 0 =
    G0.successor (G0.veblen (G0.ofNat 2) G0.zero) := by native_decide
example : G0.veblenSuccSequence G0.one (G0.ofNat 2) G0.zero 1 <
    G0.veblen (G0.ofNat 2) G0.one := by native_decide

example :
    (⨆ n, G0.eval (G0.veblenSuccSequence G0.zero G0.one G0.zero n)) =
      Ordinal.veblen 1 1 := by
  have h := G0.veblenSuccSequence_iSup_eval
    (index := G0.one) (lower := G0.zero) (arg := G0.one) (beta := G0.zero)
    (by native_decide) (by native_decide)
  simpa only [G0.eval_veblen, G0.eval_one] using h

example (index lower arg beta : G0)
    (hi : G0.predecessor? index = some lower)
    (ha : G0.predecessor? arg = some beta) :
    (ClassificationResult.limit (G0.veblenSuccSequence lower index beta)).Satisfies
      G0.notationSystem (G0.veblen index arg) :=
  (G0.veblenSuccLimitSequenceData hi ha).satisfies

end Examples
end OrdinalAnalysis
