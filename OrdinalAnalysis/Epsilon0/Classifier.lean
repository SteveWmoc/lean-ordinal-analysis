import OrdinalAnalysis.Generic.Classifier
import OrdinalAnalysis.Epsilon0.NotationSystem

/-!
# The ε₀ fundamental-sequence classifier as a generic classifier

This file adapts the existing ε₀ classifier to the generic
`OrdinalClassifier` interface. The original `FundamentalSequenceResult` and
`fundamentalSequence` API remain unchanged.
-/

namespace OrdinalAnalysis
namespace E0

open Ordinal Order

/-- Convert the existing ε₀ classifier output to the generic result type. -/
def toClassificationResult :
    FundamentalSequenceResult → ClassificationResult E0
  | .zero => .zero
  | .succ predecessor => .succ predecessor
  | .limit seq => .limit seq

/-- The conversion preserves the semantic classifier specification. -/
theorem toClassificationResult_satisfies
    {a : E0} {r : FundamentalSequenceResult}
    (h : r.Satisfies a) :
    (toClassificationResult r).Satisfies notationSystem a := by
  cases r with
  | zero =>
      change eval a = 0 at h
      change notationSystem.eval a = 0
      exact h
  | succ predecessor =>
      change eval a = Order.succ (eval predecessor) at h
      change
        notationSystem.eval a =
          Order.succ (notationSystem.eval predecessor)
      exact h
  | limit seq =>
      change
        Order.IsSuccLimit (eval a) ∧
          (∀ i, seq i < seq (i + 1) ∧ seq i < a) ∧
          ∀ α, α < eval a → ∃ i, α < eval (seq i)
        at h
      change
        Order.IsSuccLimit (notationSystem.eval a) ∧
          (∀ i, seq i < seq (i + 1) ∧ seq i < a) ∧
          ∀ α, α < notationSystem.eval a →
            ∃ i, α < notationSystem.eval (seq i)
      exact h

/-- The existing ε₀ algorithm packaged as a generic certified classifier. -/
def classifier : OrdinalClassifier notationSystem where
  classify a := toClassificationResult (fundamentalSequence a)
  satisfies a :=
    toClassificationResult_satisfies (fundamentalSequence_has_prop a)

@[simp]
theorem classifier_classify (a : E0) :
    classifier.classify a =
      toClassificationResult (fundamentalSequence a) :=
  rfl

end E0
end OrdinalAnalysis
