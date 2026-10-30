import OrdinalAnalysis.Gamma0.VeblenApplication
import OrdinalAnalysis.Gamma0.LimitSequence

/-!
# Veblen application at a limit argument

For a fixed index, φ_index is normal. Applying the executable canonical
Veblen constructor to a certified argument sequence therefore gives a certified
sequence at the corresponding Veblen value.

This implements the argument-limit rule. Successor-argument and limit-index
rules remain separate extensions.
-/

namespace OrdinalAnalysis
namespace G0

/-- Lift a certified sequence through Veblen application at any fixed canonical index. -/
def LimitSequenceData.veblenRight {a : G0} (data : LimitSequenceData a)
    (index : G0) : LimitSequenceData (veblen index a) where
  seq n := veblen index (data.seq n)
  isSuccLimit := by
    rw [eval_veblen]
    exact (Ordinal.isNormal_veblen (eval index)).map_isSuccLimit data.isSuccLimit
  strictMono := (veblen_right_strictMono index).comp data.strictMono
  lt n := veblen_right_strictMono index (data.lt n)
  cofinal := by
    intro α hα
    have hα' : α < Ordinal.veblen (eval index) (eval a) := by
      simpa only [eval_veblen] using hα
    obtain ⟨β, hβ, hαβ⟩ :=
      ((Ordinal.isNormal_veblen (eval index)).lt_iff_exists_lt data.isSuccLimit).1 hα'
    obtain ⟨n, hn⟩ := data.cofinal β hβ
    refine ⟨n, ?_⟩
    calc
      α < Ordinal.veblen (eval index) β := hαβ
      _ < Ordinal.veblen (eval index) (eval (data.seq n)) :=
        Ordinal.veblen_right_strictMono (eval index) hn
      _ = eval (veblen index (data.seq n)) := (eval_veblen index (data.seq n)).symm

/-- The lifted sequence computes pointwise by canonical Veblen application. -/
@[simp]
theorem LimitSequenceData.veblenRight_seq {a : G0} (data : LimitSequenceData a)
    (index : G0) (n : Nat) :
    (data.veblenRight index).seq n = veblen index (data.seq n) :=
  rfl

/-- Every lifted sequence has the expected Veblen supremum. -/
theorem LimitSequenceData.veblenRight_iSup_eval {a : G0} (data : LimitSequenceData a)
    (index : G0) :
    (⨆ n, eval (veblen index (data.seq n))) =
      Ordinal.veblen (eval index) (eval a) := by
  have h := (data.veblenRight index).iSup_eval
  simpa only [veblenRight_seq, eval_veblen] using h

end G0
end OrdinalAnalysis
