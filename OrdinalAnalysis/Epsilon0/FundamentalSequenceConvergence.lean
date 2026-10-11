import OrdinalAnalysis.Epsilon0.FundamentalSequenceAPI

/-!
# Convergence of ε₀ fundamental sequences

For a notation classified as a limit, the semantic values of its fundamental
sequence have supremum exactly the ordinal represented by the notation.

The proof uses the two complementary facts exposed by the fundamental-sequence
API: every sequence entry lies below the input notation, and the sequence is
semantically cofinal below the represented limit ordinal.
-/

namespace OrdinalAnalysis
namespace E0

open Ordinal

/--
The semantic values of a limit fundamental sequence converge to the ordinal
represented by the input notation.
-/
theorem fundamentalSequence_eq_limit_iSup_eval
    {a : E0} {seq : Nat → E0}
    (h : fundamentalSequence a = .limit seq) :
    (⨆ i, eval (seq i)) = eval a := by
  apply le_antisymm
  · apply Ordinal.iSup_le
    intro i
    exact ((lt_iff_eval_lt _ _).1 (fundamentalSequence_eq_limit_lt h i)).le
  · apply le_of_not_gt
    intro hgap
    obtain ⟨i, hi⟩ := fundamentalSequence_eq_limit_cofinal h hgap
    exact (not_lt_of_ge (Ordinal.le_iSup (fun i => eval (seq i)) i)) hi

end E0
end OrdinalAnalysis
