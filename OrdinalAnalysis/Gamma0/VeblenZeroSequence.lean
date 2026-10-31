import OrdinalAnalysis.Gamma0.VeblenIteration
import OrdinalAnalysis.Gamma0.Predecessor
import OrdinalAnalysis.Gamma0.LimitSequence

/-!
# First fixed points at successor Veblen indices

If index has predecessor lower, φ_index(0) is the first fixed point of
φ_lower. Iterating the executable canonical φ_lower from zero therefore
gives a strictly increasing, bounded, cofinal sequence at φ_index(0).

This covers zero arguments at successor indices. Other positive-index
arguments and limit-index rules remain later extensions.
-/

namespace OrdinalAnalysis
namespace G0

open Ordinal Order

/-- Iterate φ_lower from zero to approach its first fixed point. -/
def veblenZeroSequence (lower : G0) : Nat → G0 :=
  veblenIterate lower zero

@[simp]
theorem eval_veblenZeroSequence (lower : G0) (n : Nat) :
    eval (veblenZeroSequence lower n) =
      (Ordinal.veblen (eval lower))^[n] 0 := by
  simpa only [veblenZeroSequence, eval_zero] using eval_veblenIterate lower zero n

/-- The zero-argument value at a successor index is a next-fixed-point value. -/
theorem eval_veblen_zero_eq_nfp_of_predecessor {index lower : G0}
    (hpred : predecessor? index = some lower) :
    eval (veblen index zero) = Ordinal.nfp (Ordinal.veblen (eval lower)) 0 := by
  rw [eval_veblen, eval_zero, predecessor?_sound hpred, Order.succ_eq_add_one,
    Ordinal.veblen_add_one, Ordinal.deriv_zero_right]

theorem veblenZeroSequence_strictMono (lower : G0) :
    StrictMono (veblenZeroSequence lower) := by
  apply veblenIterate_strictMono
  apply (lt_iff_eval_lt _ _).2
  rw [eval_zero, eval_veblen, eval_zero]
  exact Ordinal.veblen_pos

theorem veblenZeroSequence_lt {index lower : G0}
    (hpred : predecessor? index = some lower) (n : Nat) :
    veblenZeroSequence lower n < veblen index zero := by
  apply (lt_iff_eval_lt _ _).2
  rw [eval_veblenZeroSequence, eval_veblen_zero_eq_nfp_of_predecessor hpred]
  exact Ordinal.iterate_lt_nfp (Ordinal.veblen_right_strictMono (eval lower))
    (show (0 : Ordinal.{0}) < Ordinal.veblen (eval lower) 0 from Ordinal.veblen_pos) n

theorem veblenZeroSequence_cofinal {index lower : G0}
    (hpred : predecessor? index = some lower) (α : Ordinal.{0})
    (hα : α < eval (veblen index zero)) :
    ∃ n, α < eval (veblenZeroSequence lower n) := by
  rw [eval_veblen_zero_eq_nfp_of_predecessor hpred] at hα
  obtain ⟨n, hn⟩ := Ordinal.lt_nfp_iff.1 hα
  exact ⟨n, by simpa only [eval_veblenZeroSequence] using hn⟩

/-- Certified first-fixed-point sequence at every canonical successor index. -/
def veblenZeroLimitSequenceData {index lower : G0}
    (hpred : predecessor? index = some lower) : LimitSequenceData (veblen index zero) where
  seq := veblenZeroSequence lower
  isSuccLimit := by
    rw [eval_veblen, eval_zero]
    have hpos : (0 : Ordinal.{0}) < eval index :=
      lt_of_le_of_lt zero_le ((lt_iff_eval_lt lower index).1 (predecessor?_lt hpred))
    have hfixed :
        ω ^ Ordinal.veblen (eval index) 0 = Ordinal.veblen (eval index) 0 := by
      simpa only [Ordinal.veblen_zero_apply] using
        Ordinal.veblen_veblen_of_lt hpos 0
    exact hfixed ▸ Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0
      (show Ordinal.veblen (eval index) 0 ≠ 0 from Ordinal.veblen_pos.ne')
  strictMono := veblenZeroSequence_strictMono lower
  lt := veblenZeroSequence_lt hpred
  cofinal := veblenZeroSequence_cofinal hpred

@[simp]
theorem veblenZeroLimitSequenceData_seq {index lower : G0}
    (hpred : predecessor? index = some lower) (n : Nat) :
    (veblenZeroLimitSequenceData hpred).seq n = veblenZeroSequence lower n :=
  rfl

/-- Supremum convergence of the executable first-fixed-point iteration. -/
theorem veblenZeroSequence_iSup_eval {index lower : G0}
    (hpred : predecessor? index = some lower) :
    (⨆ n, eval (veblenZeroSequence lower n)) = eval (veblen index zero) := by
  have h := (veblenZeroLimitSequenceData hpred).iSup_eval
  simpa only [veblenZeroLimitSequenceData_seq] using h

end G0
end OrdinalAnalysis
