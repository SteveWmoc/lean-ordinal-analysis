import OrdinalAnalysis.Generic.OrdinalNotationSystem
import Mathlib.Order.SuccPred.Limit

/-!
# Generic zero/successor/limit classifiers

This file abstracts the semantic shape of an ordinal classifier independently
of any concrete notation syntax.

A classifier returns one of three kinds of data: zero, a predecessor for a
successor notation, or a sequence for a limit notation. Its correctness is
stated entirely through the semantic map of an `OrdinalNotationSystem`.
-/

namespace OrdinalAnalysis

universe u

/-- The three semantic cases returned by a generic ordinal classifier. -/
inductive ClassificationResult (N : Type u) where
  | zero
  | succ (predecessor : N)
  | limit (seq : Nat → N)

namespace ClassificationResult

variable {N : Type u} [LinearOrder N]

/--
The semantic specification for a generic classification result.

In the limit branch the returned sequence is strictly increasing one step at
a time, stays below the classified notation, and is semantically cofinal below
its represented ordinal.
-/
def Satisfies
    (system : OrdinalNotationSystem N) (a : N) :
    ClassificationResult N → Prop
  | .zero =>
      system.eval a = 0
  | .succ predecessor =>
      system.eval a = Order.succ (system.eval predecessor)
  | .limit seq =>
      Order.IsSuccLimit (system.eval a) ∧
        (∀ i, seq i < seq (i + 1) ∧ seq i < a) ∧
        ∀ α, α < system.eval a → ∃ i, α < system.eval (seq i)

end ClassificationResult

/--
A zero/successor/limit classifier certified against a verified ordinal notation
system.

The classifier itself may be implemented however the concrete notation system
requires. The generic layer records only its output and semantic correctness.
-/
structure OrdinalClassifier
    {N : Type u} [LinearOrder N]
    (system : OrdinalNotationSystem N) where
  classify : N → ClassificationResult N
  satisfies : ∀ a, (classify a).Satisfies system a

namespace OrdinalClassifier

variable {N : Type u} [LinearOrder N]
variable {system : OrdinalNotationSystem N}

/-- The result returned by a certified classifier satisfies its semantic specification. -/
theorem classify_satisfies
    (classifier : OrdinalClassifier system) (a : N) :
    (classifier.classify a).Satisfies system a :=
  classifier.satisfies a

end OrdinalClassifier
end OrdinalAnalysis
