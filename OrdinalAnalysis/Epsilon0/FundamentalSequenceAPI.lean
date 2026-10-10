import OrdinalAnalysis.Epsilon0.FundamentalSequence

/-!
# Convenience API for ε₀ fundamental sequences

`FundamentalSequence.lean` constructs the transported classifier and proves one
semantic specification theorem for the result. This file exposes the most
useful branch-specific consequences as named theorems so callers do not need to
unpack `FundamentalSequenceResult.Satisfies` by hand.
-/

namespace OrdinalAnalysis
namespace E0

open Ordinal Order

private theorem fundamentalSequence_satisfies_of_eq
    {a : E0} {r : FundamentalSequenceResult}
    (h : fundamentalSequence a = r) :
    r.Satisfies a := by
  rw [← h]
  exact fundamentalSequence_has_prop a

/-- If the classifier returns `zero`, the input evaluates to ordinal zero. -/
theorem fundamentalSequence_eq_zero_eval
    {a : E0} (h : fundamentalSequence a = .zero) :
    eval a = 0 := by
  have hs := fundamentalSequence_satisfies_of_eq h
  change eval a = 0 at hs
  exact hs

/-- If the classifier returns `zero`, the canonical notation itself is zero. -/
theorem eq_zero_of_fundamentalSequence_eq_zero
    {a : E0} (h : fundamentalSequence a = .zero) :
    a = 0 := by
  change a = E0.zero
  apply eval_injective
  rw [eval_zero]
  exact fundamentalSequence_eq_zero_eval h

/-- If the classifier returns a successor, the input has the advertised semantics. -/
theorem fundamentalSequence_eq_succ_eval
    {a predecessor : E0}
    (h : fundamentalSequence a = .succ predecessor) :
    eval a = Order.succ (eval predecessor) := by
  have hs := fundamentalSequence_satisfies_of_eq h
  change eval a = Order.succ (eval predecessor) at hs
  exact hs

/-- The predecessor returned in the successor branch is strictly below the input notation. -/
theorem fundamentalSequence_predecessor_lt
    {a predecessor : E0}
    (h : fundamentalSequence a = .succ predecessor) :
    predecessor < a := by
  apply (lt_iff_eval_lt _ _).2
  rw [fundamentalSequence_eq_succ_eval h]
  exact Order.lt_succ _

private theorem fundamentalSequence_limit_spec
    {a : E0} {seq : Nat → E0}
    (h : fundamentalSequence a = .limit seq) :
    IsSuccLimit (eval a) ∧
      (∀ i, seq i < seq (i + 1) ∧ seq i < a) ∧
      ∀ α, α < eval a → ∃ i, α < eval (seq i) := by
  have hs := fundamentalSequence_satisfies_of_eq h
  change
    IsSuccLimit (eval a) ∧
      (∀ i, seq i < seq (i + 1) ∧ seq i < a) ∧
      ∀ α, α < eval a → ∃ i, α < eval (seq i)
    at hs
  exact hs

/-- A result in the limit branch really denotes a limit ordinal. -/
theorem fundamentalSequence_eq_limit_isSuccLimit
    {a : E0} {seq : Nat → E0}
    (h : fundamentalSequence a = .limit seq) :
    IsSuccLimit (eval a) :=
  (fundamentalSequence_limit_spec h).1

/-- Consecutive entries of a limit fundamental sequence are strictly increasing. -/
theorem fundamentalSequence_eq_limit_step_lt
    {a : E0} {seq : Nat → E0}
    (h : fundamentalSequence a = .limit seq) (i : Nat) :
    seq i < seq (i + 1) :=
  (fundamentalSequence_limit_spec h).2.1 i |>.1

/-- A limit fundamental sequence is strictly monotone. -/
theorem fundamentalSequence_eq_limit_strictMono
    {a : E0} {seq : Nat → E0}
    (h : fundamentalSequence a = .limit seq) :
    StrictMono seq :=
  strictMono_nat_of_lt_succ fun i =>
    fundamentalSequence_eq_limit_step_lt h i

/-- Every entry of a limit fundamental sequence lies below the represented notation. -/
theorem fundamentalSequence_eq_limit_lt
    {a : E0} {seq : Nat → E0}
    (h : fundamentalSequence a = .limit seq) (i : Nat) :
    seq i < a :=
  (fundamentalSequence_limit_spec h).2.1 i |>.2

/-- The semantic values of a limit fundamental sequence are cofinal below the input ordinal. -/
theorem fundamentalSequence_eq_limit_cofinal
    {a : E0} {seq : Nat → E0}
    (h : fundamentalSequence a = .limit seq)
    {α : Ordinal} (hα : α < eval a) :
    ∃ i, α < eval (seq i) :=
  (fundamentalSequence_limit_spec h).2.2 α hα

end E0
end OrdinalAnalysis
