import OrdinalAnalysis.Gamma0.VeblenLimitSequence
import OrdinalAnalysis.Gamma0.OmegaMultipleSequence

/-!
# Executable Veblen application and argument-limit examples
-/

namespace OrdinalAnalysis
namespace Examples

open Ordinal

-- Both the principal-construction and fixed-point-collapse branches execute.
example : G0.veblen G0.zero G0.zero = G0.one := by native_decide
example : G0.veblen G0.zero G0.one = G0.omega := by native_decide
example : G0.veblen G0.one G0.zero = G0.epsilonZero := by native_decide
example : G0.veblen G0.zero G0.epsilonZero = G0.epsilonZero := by native_decide

-- Lifting the natural-number sequence gives 1, ω, ω², ... at ω^ω.
example :
    ((G0.omegaMultipleLimitSequenceData 0).veblenRight G0.zero).seq 0 =
      G0.one := by native_decide
example :
    ((G0.omegaMultipleLimitSequenceData 0).veblenRight G0.zero).seq 1 =
      G0.omega := by native_decide

-- The same rule at index one starts with ε₀ and approaches φ₁(ω).
example :
    ((G0.omegaMultipleLimitSequenceData 0).veblenRight G0.one).seq 0 =
      G0.epsilonZero := by native_decide

-- Repeated lifting remains executable.
example :
    (((G0.omegaMultipleLimitSequenceData 0).veblenRight G0.zero).veblenRight
      G0.zero).seq 0 = G0.omega := by native_decide

example (a index : G0) (data : G0.LimitSequenceData a) :
    (⨆ n, G0.eval (G0.veblen index (data.seq n))) =
      Ordinal.veblen (G0.eval index) (G0.eval a) :=
  data.veblenRight_iSup_eval index

example (a index : G0) (data : G0.LimitSequenceData a) :
    (ClassificationResult.limit (data.veblenRight index).seq).Satisfies
      G0.notationSystem (G0.veblen index a) :=
  (data.veblenRight index).satisfies

end Examples
end OrdinalAnalysis
