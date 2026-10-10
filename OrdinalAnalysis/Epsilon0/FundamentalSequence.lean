import OrdinalAnalysis.Epsilon0.Completeness

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
  | succ (predecessor : E0)
  | limit (seq : Nat → E0)

/-- The semantic specification for a fundamental-sequence result. -/
def FundamentalSequenceResult.Satisfies
    (a : E0) : FundamentalSequenceResult → Prop
  | .zero =>
      eval a = 0
  | .succ predecessor =>
      eval a = Order.succ (eval predecessor)
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
  have heval : ONote.repr o.1 = eval a := by
    simpa [o, NONote.repr] using repr_toNONote a
  have hprop := ONote.fundamentalSequence_has_prop o.1
  cases hfs : ONote.fundamentalSequence o.1 with
  | inl opt =>
      cases opt with
      | none =>
          rw [hfs, ONote.FundamentalSequenceProp] at hprop
          refine ⟨.zero, ?_⟩
          change eval a = 0
          calc
            eval a = ONote.repr o.1 := heval.symm
            _ = ONote.repr 0 := congrArg ONote.repr hprop
            _ = 0 := ONote.repr_zero
      | some predecessor =>
          rw [hfs, ONote.FundamentalSequenceProp] at hprop
          let predecessor' : NONote := ⟨predecessor, hprop.2 hnf⟩
          have hpredEval :
              eval (ofNONote predecessor') = ONote.repr predecessor := by
            rw [eval_ofNONote]
            rfl
          refine ⟨.succ (ofNONote predecessor'), ?_⟩
          change eval a = Order.succ (eval (ofNONote predecessor'))
          calc
            eval a = ONote.repr o.1 := heval.symm
            _ = Order.succ (ONote.repr predecessor) := hprop.1
            _ = Order.succ (eval (ofNONote predecessor')) :=
              congrArg Order.succ hpredEval.symm
  | inr seq =>
      rw [hfs, ONote.FundamentalSequenceProp] at hprop
      let seq' : Nat → E0 := fun i =>
        ofNONote ⟨seq i, (hprop.2.1 i).2.2 hnf⟩
      have hevalSeq (i : Nat) :
          eval (seq' i) = ONote.repr (seq i) := by
        dsimp [seq']
        rw [eval_ofNONote]
        rfl
      refine ⟨.limit seq', ?_⟩
      change
        IsSuccLimit (eval a) ∧
          (∀ i, seq' i < seq' (i + 1) ∧ seq' i < a) ∧
          ∀ α, α < eval a → ∃ i, α < eval (seq' i)
      refine ⟨?_, ?_, ?_⟩
      · simpa [heval] using hprop.1
      · intro i
        constructor
        · apply (lt_iff_eval_lt _ _).2
          calc
            eval (seq' i) = ONote.repr (seq i) := hevalSeq i
            _ < ONote.repr (seq (i + 1)) :=
              (ONote.lt_def).1 (hprop.2.1 i).1
            _ = eval (seq' (i + 1)) := (hevalSeq (i + 1)).symm
        · apply (lt_iff_eval_lt _ _).2
          calc
            eval (seq' i) = ONote.repr (seq i) := hevalSeq i
            _ < ONote.repr o.1 :=
              (ONote.lt_def).1 (hprop.2.1 i).2.1
            _ = eval a := heval
      · intro α hα
        have hα' : α < ONote.repr o.1 := by
          simpa [heval] using hα
        obtain ⟨i, hi⟩ := hprop.2.2 α hα'
        refine ⟨i, ?_⟩
        calc
          α < ONote.repr (seq i) := hi
          _ = eval (seq' i) := (hevalSeq i).symm

/-- The executable fundamental-sequence classifier on canonical `E0`. -/
def fundamentalSequence (a : E0) : FundamentalSequenceResult :=
  (fundamentalSequenceData a).result

/-- The transported algorithm satisfies the expected zero/successor/limit specification. -/
theorem fundamentalSequence_has_prop (a : E0) :
    (fundamentalSequence a).Satisfies a :=
  (fundamentalSequenceData a).satisfies

end E0
end OrdinalAnalysis
