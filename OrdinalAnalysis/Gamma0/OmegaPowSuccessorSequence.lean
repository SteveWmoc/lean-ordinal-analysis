import OrdinalAnalysis.Gamma0.PrincipalMultiple
import OrdinalAnalysis.Gamma0.Predecessor
import OrdinalAnalysis.Gamma0.LimitSequence

/-!
# The successor-exponent rule for powers of ω

When a has canonical predecessor b, finite multiples of ω^(eval b) give a
certified executable sequence at ω^(eval a). Normalized Veblen multiplication
also handles fixed-point predecessors such as ε₀.
-/

namespace OrdinalAnalysis
namespace G0

open Ordinal Order

/-- The sequence of finite multiples of ω^(eval b). -/
def omegaPowSuccSequence (b : G0) : Nat → G0 :=
  veblenMulNat zero b

@[simp]
theorem eval_omegaPowSuccSequence (b : G0) (n : Nat) :
    eval (omegaPowSuccSequence b n) = ω ^ eval b * (n : Ordinal.{0}) := by
  simp only [omegaPowSuccSequence, eval_veblenMulNat, eval_zero,
    Ordinal.veblen_zero_apply]

theorem omegaPowSuccSequence_strictMono (b : G0) :
    StrictMono (omegaPowSuccSequence b) := by
  intro m n hmn
  apply (lt_iff_eval_lt _ _).2
  rw [eval_omegaPowSuccSequence, eval_omegaPowSuccSequence]
  apply (Ordinal.isNormal_mul_right (Ordinal.opow_pos (eval b) Ordinal.omega0_pos)).strictMono
  exact_mod_cast hmn

theorem omegaPowSuccSequence_lt {a b : G0}
    (hpred : predecessor? a = some b) (n : Nat) :
    omegaPowSuccSequence b n < veblen zero a := by
  apply (lt_iff_eval_lt _ _).2
  rw [eval_omegaPowSuccSequence, eval_veblen, eval_zero, Ordinal.veblen_zero_apply]
  exact Ordinal.opow_mul_lt_opow (Ordinal.natCast_lt_omega0 n)
    ((lt_iff_eval_lt b a).1 (predecessor?_lt hpred))

theorem omegaPowSuccSequence_cofinal {a b : G0}
    (hpred : predecessor? a = some b) (α : Ordinal.{0})
    (hα : α < eval (veblen zero a)) :
    ∃ n, α < eval (omegaPowSuccSequence b n) := by
  rw [eval_veblen, eval_zero, Ordinal.veblen_zero_apply,
    predecessor?_sound hpred, Order.succ_eq_add_one, Ordinal.opow_add_one] at hα
  obtain ⟨d, hd, hαd⟩ :=
    (Ordinal.lt_mul_iff_of_isSuccLimit Ordinal.isSuccLimit_omega0).1 hα
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 hd
  exact ⟨n, by simpa only [eval_omegaPowSuccSequence] using hαd⟩

/-- A certified sequence at φ₀(a) when a is a successor with predecessor b. -/
def omegaPowSuccLimitSequenceData {a b : G0}
    (hpred : predecessor? a = some b) : LimitSequenceData (veblen zero a) where
  seq := omegaPowSuccSequence b
  isSuccLimit := by
    rw [eval_veblen, eval_zero, Ordinal.veblen_zero_apply]
    apply Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0
    exact (lt_of_le_of_lt (show (0 : Ordinal.{0}) ≤ eval b from zero_le)
      ((lt_iff_eval_lt b a).1 (predecessor?_lt hpred))).ne'
  strictMono := omegaPowSuccSequence_strictMono b
  lt := omegaPowSuccSequence_lt hpred
  cofinal := omegaPowSuccSequence_cofinal hpred

/-- The certificate retains the executable successor-exponent sequence. -/
@[simp]
theorem omegaPowSuccLimitSequenceData_seq {a b : G0}
    (hpred : predecessor? a = some b) (n : Nat) :
    (omegaPowSuccLimitSequenceData hpred).seq n = omegaPowSuccSequence b n :=
  rfl

/-- Supremum convergence of the successor-exponent sequence. -/
theorem omegaPowSuccSequence_iSup_eval {a b : G0}
    (hpred : predecessor? a = some b) :
    (⨆ n, eval (omegaPowSuccSequence b n)) = ω ^ eval a := by
  have h := (omegaPowSuccLimitSequenceData hpred).iSup_eval
  simpa only [omegaPowSuccLimitSequenceData_seq, eval_veblen, eval_zero,
    Ordinal.veblen_zero_apply] using h

end G0
end OrdinalAnalysis
