import OrdinalAnalysis.Epsilon0.FundamentalSequenceConvergence

/-!
# Ergonomic API for limit fundamental sequences below ε₀

This file packages the limit branch of the fundamental-sequence classifier as
a certified object. Callers who already know that `eval a` is a limit ordinal
can work directly with its sequence and the standard fundamental-sequence
properties without carrying an equality against `FundamentalSequenceResult.limit`.
-/

namespace OrdinalAnalysis
namespace E0

open Ordinal Order

/--
A certified fundamental sequence for an `E0` notation whose semantic value is
a limit ordinal.
-/
structure LimitFundamentalSequenceData (a : E0) where
  seq : Nat → E0
  strictMono : StrictMono seq
  lt : ∀ i, seq i < a
  cofinal : ∀ {α : Ordinal}, α < eval a → ∃ i, α < eval (seq i)
  iSup_eval : (⨆ i, eval (seq i)) = eval a

/--
Extract the certified limit fundamental sequence from the executable
classifier, discharging the impossible zero and successor branches
semantically.
-/
def limitFundamentalSequenceData
    (a : E0) (hlim : IsSuccLimit (eval a)) :
    LimitFundamentalSequenceData a := by
  cases hfs : fundamentalSequence a with
  | zero =>
      have hzero : eval a = 0 := fundamentalSequence_eq_zero_eval hfs
      exact False.elim <| Ordinal.not_isSuccLimit_zero (hzero ▸ hlim)
  | succ predecessor =>
      have hsucc : eval a = Order.succ (eval predecessor) :=
        fundamentalSequence_eq_succ_eval hfs
      exact False.elim <|
        Order.not_isSuccLimit_succ (eval predecessor) (hsucc ▸ hlim)
  | limit seq =>
      exact
        { seq := seq
          strictMono := fundamentalSequence_eq_limit_strictMono hfs
          lt := fundamentalSequence_eq_limit_lt hfs
          cofinal := fundamentalSequence_eq_limit_cofinal hfs
          iSup_eval := fundamentalSequence_eq_limit_iSup_eval hfs }

/-- The canonical fundamental sequence associated to a semantic limit notation. -/
def limitFundamentalSequence
    (a : E0) (hlim : IsSuccLimit (eval a)) : Nat → E0 :=
  (limitFundamentalSequenceData a hlim).seq

/-- The canonical limit fundamental sequence is strictly increasing. -/
theorem limitFundamentalSequence_strictMono
    (a : E0) (hlim : IsSuccLimit (eval a)) :
    StrictMono (limitFundamentalSequence a hlim) := by
  simpa [limitFundamentalSequence] using
    (limitFundamentalSequenceData a hlim).strictMono

/-- Every entry of the canonical limit fundamental sequence lies below the input. -/
theorem limitFundamentalSequence_lt
    (a : E0) (hlim : IsSuccLimit (eval a)) (i : Nat) :
    limitFundamentalSequence a hlim i < a := by
  simpa [limitFundamentalSequence] using
    (limitFundamentalSequenceData a hlim).lt i

/--
The canonical limit fundamental sequence is semantically cofinal below the
ordinal represented by the input.
-/
theorem limitFundamentalSequence_cofinal
    (a : E0) (hlim : IsSuccLimit (eval a))
    {α : Ordinal} (hα : α < eval a) :
    ∃ i, α < eval (limitFundamentalSequence a hlim i) := by
  simpa [limitFundamentalSequence] using
    (limitFundamentalSequenceData a hlim).cofinal hα

/--
The semantic values of the canonical limit fundamental sequence have supremum
exactly the ordinal represented by the input.
-/
theorem limitFundamentalSequence_iSup_eval
    (a : E0) (hlim : IsSuccLimit (eval a)) :
    (⨆ i, eval (limitFundamentalSequence a hlim i)) = eval a := by
  simpa [limitFundamentalSequence] using
    (limitFundamentalSequenceData a hlim).iSup_eval

end E0
end OrdinalAnalysis
