import OrdinalAnalysis.Generic.ClassifierConsequences

/-!
# Ergonomic generic API for limit sequences

This file packages the limit branch of any certified `OrdinalClassifier` as a
proof-carrying object. Once a caller knows semantically that a notation
represents a limit ordinal, the zero and successor branches are impossible and
the classifier's returned sequence can be used directly without carrying a
branch equality through every theorem.
-/

namespace OrdinalAnalysis
namespace OrdinalClassifier

universe u

variable {N : Type u} [LinearOrder N]
variable {system : OrdinalNotationSystem N}

/--
A certified limit sequence returned by a generic ordinal classifier.
-/
structure LimitSequenceData
    (classifier : OrdinalClassifier system) (a : N) where
  seq : Nat → N
  strictMono : StrictMono seq
  lt : ∀ i, seq i < a
  cofinal :
    ∀ {α : Ordinal}, α < system.eval a →
      ∃ i, α < system.eval (seq i)
  iSup_eval :
    (⨆ i, system.eval (seq i)) = system.eval a

/--
Extract the certified limit sequence from a generic classifier, discharging
the impossible zero and successor branches from a semantic limit hypothesis.
-/
def limitSequenceData
    (classifier : OrdinalClassifier system)
    (a : N) (hlim : Order.IsSuccLimit (system.eval a)) :
    LimitSequenceData classifier a := by
  cases hfs : classifier.classify a with
  | zero =>
      have hzero : system.eval a = 0 :=
        classifier.classify_eq_zero_eval hfs
      exact False.elim <|
        Ordinal.not_isSuccLimit_zero (hzero ▸ hlim)
  | succ predecessor =>
      have hsucc :
          system.eval a = Order.succ (system.eval predecessor) :=
        classifier.classify_eq_succ_eval hfs
      exact False.elim <|
        Order.not_isSuccLimit_succ
          (system.eval predecessor) (hsucc ▸ hlim)
  | limit seq =>
      exact
        { seq := seq
          strictMono := classifier.classify_eq_limit_strictMono hfs
          lt := classifier.classify_eq_limit_lt hfs
          cofinal := classifier.classify_eq_limit_cofinal hfs
          iSup_eval := classifier.classify_eq_limit_iSup_eval hfs }

/-- The canonical sequence selected by a classifier for a semantic limit notation. -/
def limitSequence
    (classifier : OrdinalClassifier system)
    (a : N) (hlim : Order.IsSuccLimit (system.eval a)) :
    Nat → N :=
  (classifier.limitSequenceData a hlim).seq

/-- The canonical generic limit sequence is strictly increasing. -/
theorem limitSequence_strictMono
    (classifier : OrdinalClassifier system)
    (a : N) (hlim : Order.IsSuccLimit (system.eval a)) :
    StrictMono (classifier.limitSequence a hlim) := by
  simpa [limitSequence] using
    (classifier.limitSequenceData a hlim).strictMono

/-- Every entry of the canonical generic limit sequence lies below its input notation. -/
theorem limitSequence_lt
    (classifier : OrdinalClassifier system)
    (a : N) (hlim : Order.IsSuccLimit (system.eval a))
    (i : Nat) :
    classifier.limitSequence a hlim i < a := by
  simpa [limitSequence] using
    (classifier.limitSequenceData a hlim).lt i

/--
The semantic values of the canonical generic limit sequence are cofinal below
the ordinal represented by its input.
-/
theorem limitSequence_cofinal
    (classifier : OrdinalClassifier system)
    (a : N) (hlim : Order.IsSuccLimit (system.eval a))
    {α : Ordinal} (hα : α < system.eval a) :
    ∃ i, α < system.eval (classifier.limitSequence a hlim i) := by
  simpa [limitSequence] using
    (classifier.limitSequenceData a hlim).cofinal hα

/--
The semantic values of the canonical generic limit sequence have supremum
exactly the ordinal represented by its input.
-/
theorem limitSequence_iSup_eval
    (classifier : OrdinalClassifier system)
    (a : N) (hlim : Order.IsSuccLimit (system.eval a)) :
    (⨆ i, system.eval (classifier.limitSequence a hlim i)) =
      system.eval a := by
  simpa [limitSequence] using
    (classifier.limitSequenceData a hlim).iSup_eval

end OrdinalClassifier
end OrdinalAnalysis
