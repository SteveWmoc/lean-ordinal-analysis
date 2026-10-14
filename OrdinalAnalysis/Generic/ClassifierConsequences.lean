import OrdinalAnalysis.Generic.Classifier
import Mathlib.SetTheory.Ordinal.Family

/-!
# Generic consequences of a certified ordinal classifier

This file derives the branch-specific API shared by every certified
`OrdinalClassifier`.

The zero branch is kept semantic: the generic notation type need not carry a
distinguished syntactic zero. Successor and limit consequences use only the
verified notation order and semantic evaluation supplied by
`OrdinalNotationSystem`.
-/

namespace OrdinalAnalysis
namespace OrdinalClassifier

universe u

variable {N : Type u} [LinearOrder N]
variable {system : OrdinalNotationSystem N}

private theorem satisfies_of_classify_eq
    (classifier : OrdinalClassifier system)
    {a : N} {r : ClassificationResult N}
    (h : classifier.classify a = r) :
    r.Satisfies system a := by
  rw [← h]
  exact classifier.classify_satisfies a

/-- If the classifier returns `zero`, the input evaluates to ordinal zero. -/
theorem classify_eq_zero_eval
    (classifier : OrdinalClassifier system)
    {a : N} (h : classifier.classify a = .zero) :
    system.eval a = 0 := by
  have hs := classifier.satisfies_of_classify_eq h
  change system.eval a = 0 at hs
  exact hs

/-- A successor result has the advertised ordinal-successor semantics. -/
theorem classify_eq_succ_eval
    (classifier : OrdinalClassifier system)
    {a predecessor : N}
    (h : classifier.classify a = .succ predecessor) :
    system.eval a = Order.succ (system.eval predecessor) := by
  have hs := classifier.satisfies_of_classify_eq h
  change
    system.eval a = Order.succ (system.eval predecessor)
    at hs
  exact hs

/-- The predecessor returned in the successor branch is strictly below the input notation. -/
theorem classify_predecessor_lt
    (classifier : OrdinalClassifier system)
    {a predecessor : N}
    (h : classifier.classify a = .succ predecessor) :
    predecessor < a := by
  apply (system.lt_iff_eval_lt _ _).2
  rw [classifier.classify_eq_succ_eval h]
  exact Order.lt_succ _

private theorem classify_limit_spec
    (classifier : OrdinalClassifier system)
    {a : N} {seq : Nat → N}
    (h : classifier.classify a = .limit seq) :
    Order.IsSuccLimit (system.eval a) ∧
      (∀ i, seq i < seq (i + 1) ∧ seq i < a) ∧
      ∀ α, α < system.eval a → ∃ i, α < system.eval (seq i) := by
  have hs := classifier.satisfies_of_classify_eq h
  change
    Order.IsSuccLimit (system.eval a) ∧
      (∀ i, seq i < seq (i + 1) ∧ seq i < a) ∧
      ∀ α, α < system.eval a → ∃ i, α < system.eval (seq i)
    at hs
  exact hs

/-- A result in the limit branch really denotes a limit ordinal. -/
theorem classify_eq_limit_isSuccLimit
    (classifier : OrdinalClassifier system)
    {a : N} {seq : Nat → N}
    (h : classifier.classify a = .limit seq) :
    Order.IsSuccLimit (system.eval a) :=
  (classifier.classify_limit_spec h).1

/-- Consecutive entries of a returned limit sequence are strictly increasing. -/
theorem classify_eq_limit_step_lt
    (classifier : OrdinalClassifier system)
    {a : N} {seq : Nat → N}
    (h : classifier.classify a = .limit seq) (i : Nat) :
    seq i < seq (i + 1) :=
  (classifier.classify_limit_spec h).2.1 i |>.1

/-- A returned limit sequence is strictly monotone. -/
theorem classify_eq_limit_strictMono
    (classifier : OrdinalClassifier system)
    {a : N} {seq : Nat → N}
    (h : classifier.classify a = .limit seq) :
    StrictMono seq :=
  strictMono_nat_of_lt_succ fun i =>
    classifier.classify_eq_limit_step_lt h i

/-- Every entry of a returned limit sequence lies below the input notation. -/
theorem classify_eq_limit_lt
    (classifier : OrdinalClassifier system)
    {a : N} {seq : Nat → N}
    (h : classifier.classify a = .limit seq) (i : Nat) :
    seq i < a :=
  (classifier.classify_limit_spec h).2.1 i |>.2

/-- The semantic values of a returned limit sequence are cofinal below the input ordinal. -/
theorem classify_eq_limit_cofinal
    (classifier : OrdinalClassifier system)
    {a : N} {seq : Nat → N}
    (h : classifier.classify a = .limit seq)
    {α : Ordinal} (hα : α < system.eval a) :
    ∃ i, α < system.eval (seq i) :=
  (classifier.classify_limit_spec h).2.2 α hα

/--
The semantic values of a returned limit sequence have supremum exactly the
ordinal represented by the input notation.
-/
theorem classify_eq_limit_iSup_eval
    (classifier : OrdinalClassifier system)
    {a : N} {seq : Nat → N}
    (h : classifier.classify a = .limit seq) :
    (⨆ i, system.eval (seq i)) = system.eval a := by
  apply le_antisymm
  · apply Ordinal.iSup_le
    intro i
    exact
      ((system.lt_iff_eval_lt _ _).1
        (classifier.classify_eq_limit_lt h i)).le
  · apply le_of_not_gt
    intro hgap
    obtain ⟨i, hi⟩ := classifier.classify_eq_limit_cofinal h hgap
    exact
      (not_lt_of_ge
        (Ordinal.le_iSup (fun i => system.eval (seq i)) i)) hi

end OrdinalClassifier
end OrdinalAnalysis
