import OrdinalAnalysis.Epsilon0.Operations

/-!
# Fundamental sequences below ε₀

Mathlib's `ONote.fundamentalSequence` already classifies a notation as zero,
a successor, or a limit and, in the limit case, constructs a strictly
increasing cofinal sequence.

This file transports that construction to canonical `E0` notations.  The
normality obligations for the predecessor or sequence entries are discharged
by `ONote.fundamentalSequence_has_prop`.
-/

namespace OrdinalAnalysis
namespace E0

open Ordinal Order

/--
The three possible outputs of the fundamental-sequence algorithm.

* `zero`: the input denotes zero;
* `succ pred`: the input denotes the successor of `pred`;
* `limit seq`: the input is a limit and `seq` is its fundamental sequence.
-/
inductive FundamentalSequenceResult where
  | zero
  | succ (pred : E0)
  | limit (seq : Nat → E0)

/-- The semantic specification for a fundamental-sequence result. -/
def FundamentalSequenceResult.Satisfies
    (a : E0) : FundamentalSequenceResult → Prop
  | .zero =>
      eval a = 0
  | .succ pred =>
      eval a = Ordinal.succ (eval pred)
  | .limit seq =>
      IsSuccLimit (eval a) ∧
        (∀ i, seq i < seq (i + 1) ∧ seq i < a) ∧
        ∀ α, α < eval a → ∃ i, α < eval (seq i)

/--
The fundamental-sequence result together with its semantic correctness proof.

Keeping the proof alongside the transported data means the wrapper only has to
unpack mathlib's correctness theorem once.
-/
structure FundamentalSequenceData (a : E0) where
  result : FundamentalSequenceResult
  satisfies : result.Satisfies a

/-- Transport mathlib's fundamental-sequence algorithm to canonical `E0`. -/
def fundamentalSequenceData (a : E0) : FundamentalSequenceData a := by
  let o : NONote := toNONote a
  have hnf : ONote.NF o.1 := o.2
  have hprop := ONote.fundamentalSequence_has_prop o.1
  cases hfs : ONote.fundamentalSequence o.1 with
  | inl opt =>
      cases opt with
      | none =>
          rw [hfs, ONote.FundamentalSequenceProp] at hprop
          refine ⟨.zero, ?_⟩
          rw [← repr_toNONote a]
          change ONote.repr o.1 = 0
          rw [hprop]
          exact ONote.repr_zero
      | some pred =>
          rw [hfs, ONote.FundamentalSequenceProp] at hprop
          let pred' : NONote := ⟨pred, hprop.2 hnf⟩
          refine ⟨.succ (ofNONote pred'), ?_⟩
          rw [← repr_toNONote a, eval_ofNONote pred']
          exact hprop.1
  | inr seq =>
      rw [hfs, ONote.FundamentalSequenceProp] at hprop
      let seq' : Nat → E0 := fun i =>
        ofNONote ⟨seq i, (hprop.2.1 i).2.2 hnf⟩
      refine ⟨.limit seq', ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [← repr_toNONote a]
        exact hprop.1
      · intro i
        constructor
        · apply (lt_iff_eval_lt _ _).2
          change
            ONote.repr (seq i) <
              ONote.repr (seq (i + 1))
          exact (ONote.lt_def).1 (hprop.2.1 i).1
        · apply (lt_iff_eval_lt _ _).2
          change ONote.repr (seq i) < eval a
          rw [← repr_toNONote a]
          exact (ONote.lt_def).1 (hprop.2.1 i).2.1
      · intro α hα
        have hα' : α < ONote.repr o.1 := by
          simpa [o, NONote.repr] using hα
        obtain ⟨i, hi⟩ := hprop.2.2 α hα'
        refine ⟨i, ?_⟩
        change α < ONote.repr (seq i)
        exact hi

/-- The executable fundamental-sequence classifier on canonical `E0`. -/
def fundamentalSequence (a : E0) : FundamentalSequenceResult :=
  (fundamentalSequenceData a).result

/-- The transported algorithm satisfies the expected zero/successor/limit specification. -/
theorem fundamentalSequence_has_prop (a : E0) :
    (fundamentalSequence a).Satisfies a :=
  (fundamentalSequenceData a).satisfies

end E0
end OrdinalAnalysis
