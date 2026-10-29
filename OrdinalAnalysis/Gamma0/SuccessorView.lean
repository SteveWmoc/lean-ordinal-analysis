import OrdinalAnalysis.Gamma0.SemanticNormalForm

/-!
# Executable zero/successor/limit shape of Γ₀ terms

The rightmost summand determines whether a normal Veblen sum is a successor.
A finite final summand supplies its predecessor; every other final principal
term is a limit. This view does not yet supply fundamental sequences.
-/

namespace OrdinalAnalysis
namespace G0Term

open Ordinal Order

/-- The semantic shape of a term, with raw predecessor syntax in the successor case. -/
inductive SuccessorView where
  | zero
  | succ (predecessor : G0Term)
  | limit
deriving DecidableEq, Repr

/-- Classify a final block with zero tail. -/
def terminalSuccessorView : G0Term → G0Term → Nat → SuccessorView
  | .zero, .zero, 0 => .succ .zero
  | .zero, .zero, n + 1 => .succ (.veblen .zero .zero n .zero)
  | _, _, _ => .limit

/-- Classify finite raw syntax by following its rightmost tail. -/
def successorView : G0Term → SuccessorView
  | .zero => .zero
  | .veblen index arg coeff tail =>
      match tail with
      | .zero => terminalSuccessorView index arg coeff
      | .veblen _ _ _ _ =>
          match successorView tail with
          | .succ predecessor => .succ (.veblen index arg coeff predecessor)
          | _ => .limit

/-- Correctness includes normality of every returned predecessor. -/
def SuccessorView.Satisfies (t : G0Term) : SuccessorView → Prop
  | .zero => eval t = 0
  | .succ predecessor => IsNormal predecessor ∧ eval t = Order.succ (eval predecessor)
  | .limit => IsSuccLimit (eval t)

private theorem isSuccLimit_veblen_of_index_pos
    {index : Ordinal.{0}} (arg : Ordinal.{0}) (hindex : 0 < index) :
    IsSuccLimit (Ordinal.veblen index arg) := by
  have hfixed : ω ^ Ordinal.veblen index arg = Ordinal.veblen index arg := by
    simpa only [Ordinal.veblen_zero_apply] using
      Ordinal.veblen_veblen_of_lt hindex arg
  have hlim := Ordinal.isSuccLimit_opow_left
    Ordinal.isSuccLimit_omega0 (Ordinal.veblen_pos (o := index) (a := arg)).ne'
  exact hfixed ▸ hlim

/-- Every final block has its stated semantic shape. -/
theorem terminalSuccessorView_satisfies (index arg : G0Term) (coeff : Nat) :
    (terminalSuccessorView index arg coeff).Satisfies
      (.veblen index arg coeff .zero) := by
  cases index with
  | zero =>
      cases arg with
      | zero =>
          cases coeff with
          | zero =>
              refine ⟨isNormal_zero, ?_⟩
              simp [eval_veblen, Ordinal.veblen_zero_apply, Order.succ_eq_add_one]
          | succ n =>
              constructor
              · simp [principal]
              · simp [eval_veblen, Ordinal.veblen_zero_apply,
                  Order.succ_eq_add_one, Nat.cast_add_one]
      | veblen argIndex argArg argCoeff argTail =>
          change IsSuccLimit (eval (.veblen .zero
            (.veblen argIndex argArg argCoeff argTail) coeff .zero))
          rw [eval_veblen, eval_zero, add_zero]
          apply Ordinal.isSuccLimit_mul_left _ (by simp)
          rw [Ordinal.veblen_zero_apply]
          exact Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0
            (eval_veblen_pos argIndex argArg argCoeff argTail).ne'
  | veblen indexIndex indexArg indexCoeff indexTail =>
      change IsSuccLimit (eval (.veblen
        (.veblen indexIndex indexArg indexCoeff indexTail) arg coeff .zero))
      rw [eval_veblen, eval_zero, add_zero]
      apply Ordinal.isSuccLimit_mul_left _ (by simp)
      exact isSuccLimit_veblen_of_index_pos (eval arg)
        (eval_veblen_pos indexIndex indexArg indexCoeff indexTail)

/-- The executable shape view is correct on normal terms. -/
theorem successorView_satisfies (t : G0Term) (hn : IsNormal t) :
    (successorView t).Satisfies t := by
  induction t with
  | zero =>
      rfl
  | veblen index arg coeff tail _ _ ihTail =>
      cases tail with
      | zero =>
          exact terminalSuccessorView_satisfies index arg coeff
      | veblen tailIndex tailArg tailCoeff tailTail =>
          have htail := ihTail hn.tail
          cases hv : successorView (.veblen tailIndex tailArg tailCoeff tailTail) with
          | zero =>
              have hz : eval (.veblen tailIndex tailArg tailCoeff tailTail) = 0 := by
                simpa only [hv, SuccessorView.Satisfies] using htail
              exact ((eval_veblen_pos tailIndex tailArg tailCoeff tailTail).ne' hz).elim
          | limit =>
              rw [successorView, hv, SuccessorView.Satisfies]
              rw [eval_veblen]
              apply Ordinal.isSuccLimit_add
              simpa only [hv, SuccessorView.Satisfies] using htail
          | succ predecessor =>
              have hp : IsNormal predecessor ∧
                  eval (.veblen tailIndex tailArg tailCoeff tailTail) =
                    Order.succ (eval predecessor) := by
                simpa only [hv, SuccessorView.Satisfies] using htail
              rw [successorView, hv, SuccessorView.Satisfies]
              constructor
              · apply isNormal_veblen_of_eval_bounds coeff hn.index hn.arg hp.1
                · have hraw := (rawLT_iff_eval_lt arg (principal index arg)
                    hn.arg (IsNormal.principal hn.index hn.arg hn.arg_lt_principal)).1
                    hn.arg_lt_principal
                  simpa only [eval_principal] using hraw
                · have hpredLt : eval predecessor <
                      eval (.veblen tailIndex tailArg tailCoeff tailTail) := by
                    rw [hp.2]
                    exact lt_succ _
                  have hbound := (hasSemanticTailBounds_of_normal _ hn).tail_lt_principal
                  simpa only [eval_principal] using hpredLt.trans hbound
              · rw [eval_veblen, hp.2, eval_veblen]
                simp only [Order.succ_eq_add_one, add_assoc]

end G0Term
end OrdinalAnalysis
