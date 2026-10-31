import OrdinalAnalysis.Gamma0.VeblenZeroSequence
import OrdinalAnalysis.Gamma0.Successor

/-!
# Successor arguments at successor Veblen indices

To approach φ_(i+1)(β+1), iterate φ_i from φ_(i+1)(β)+1.
All sequence terms are computed through canonical finite syntax.
-/

namespace OrdinalAnalysis
namespace G0

open Ordinal Order

private theorem isSuccLimit_veblen_of_index_pos
    {index : Ordinal.{0}} (arg : Ordinal.{0}) (hi : 0 < index) :
    IsSuccLimit (Ordinal.veblen index arg) := by
  have hfixed : ω ^ Ordinal.veblen index arg = Ordinal.veblen index arg := by
    simpa only [Ordinal.veblen_zero_apply] using Ordinal.veblen_veblen_of_lt hi arg
  exact hfixed ▸ Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0
    (Ordinal.veblen_pos (o := index) (a := arg)).ne'

private theorem isSuccLimit_veblen_of_arg_pos
    (index : Ordinal.{0}) {arg : Ordinal.{0}} (ha : 0 < arg) :
    IsSuccLimit (Ordinal.veblen index arg) := by
  rcases eq_zero_or_pos index with hi | hi
  · rw [hi, Ordinal.veblen_zero_apply]
    exact Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 ha.ne'
  · exact isSuccLimit_veblen_of_index_pos arg hi

/-- Iterate the lower Veblen function above the preceding fixed point. -/
def veblenSuccSequence (lower index beta : G0) : Nat → G0 :=
  veblenIterate lower (successor (veblen index beta))

@[simp]
theorem eval_veblenSuccSequence (lower index beta : G0) (n : Nat) :
    eval (veblenSuccSequence lower index beta n) =
      (Ordinal.veblen (eval lower))^[n]
        (Order.succ (Ordinal.veblen (eval index) (eval beta))) := by
  simpa only [veblenSuccSequence, eval_successor, eval_veblen] using
    eval_veblenIterate lower (successor (veblen index beta)) n

/-- Identify the target with the next fixed point above the previous one. -/
theorem eval_veblen_succ_eq_nfp_of_predecessors
    {index lower arg beta : G0}
    (hi : predecessor? index = some lower)
    (ha : predecessor? arg = some beta) :
    eval (veblen index arg) =
      Ordinal.nfp (Ordinal.veblen (eval lower))
        (eval (successor (veblen index beta))) := by
  simp only [eval_successor, eval_veblen, predecessor?_sound hi,
    predecessor?_sound ha, Order.succ_eq_add_one, Ordinal.veblen_add_one,
    Ordinal.deriv_add_one]

/-- The starting successor grows strictly under the lower Veblen function. -/
theorem veblenSuccSequence_seed_lt {index lower : G0}
    (hi : predecessor? index = some lower) (beta : G0) :
    successor (veblen index beta) <
      veblen lower (successor (veblen index beta)) := by
  apply (lt_iff_eval_lt _ _).2
  simp only [eval_successor, eval_veblen]
  have hil : eval lower < eval index :=
    (lt_iff_eval_lt _ _).1 (predecessor?_lt hi)
  have hfixed := Ordinal.veblen_veblen_of_lt hil (eval beta)
  have hlt : Ordinal.veblen (eval index) (eval beta) <
      Ordinal.veblen (eval lower)
        (Order.succ (Ordinal.veblen (eval index) (eval beta))) := by
    calc
      Ordinal.veblen (eval index) (eval beta) =
          Ordinal.veblen (eval lower)
            (Ordinal.veblen (eval index) (eval beta)) := hfixed.symm
      _ < _ := Ordinal.veblen_right_strictMono (eval lower) (lt_succ _)
  exact (isSuccLimit_veblen_of_arg_pos (eval lower)
    (lt_of_le_of_lt zero_le (lt_succ _))).succ_lt hlt

theorem veblenSuccSequence_strictMono {index lower : G0}
    (hi : predecessor? index = some lower) (beta : G0) :
    StrictMono (veblenSuccSequence lower index beta) :=
  veblenIterate_strictMono lower (successor (veblen index beta))
    (veblenSuccSequence_seed_lt hi beta)

theorem veblenSuccSequence_lt {index lower arg beta : G0}
    (hi : predecessor? index = some lower)
    (ha : predecessor? arg = some beta) (n : Nat) :
    veblenSuccSequence lower index beta n < veblen index arg := by
  apply (lt_iff_eval_lt _ _).2
  rw [eval_veblen_succ_eq_nfp_of_predecessors hi ha]
  change eval (veblenIterate lower (successor (veblen index beta)) n) < _
  rw [eval_veblenIterate]
  have hseed : eval (successor (veblen index beta)) <
      Ordinal.veblen (eval lower) (eval (successor (veblen index beta))) := by
    simpa only [eval_veblen] using
      (lt_iff_eval_lt _ _).1 (veblenSuccSequence_seed_lt hi beta)
  exact Ordinal.iterate_lt_nfp (Ordinal.veblen_right_strictMono (eval lower)) hseed n

theorem veblenSuccSequence_cofinal {index lower arg beta : G0}
    (hi : predecessor? index = some lower)
    (ha : predecessor? arg = some beta)
    (alpha : Ordinal.{0}) (halpha : alpha < eval (veblen index arg)) :
    ∃ n, alpha < eval (veblenSuccSequence lower index beta n) := by
  rw [eval_veblen_succ_eq_nfp_of_predecessors hi ha] at halpha
  obtain ⟨n, hn⟩ := Ordinal.lt_nfp_iff.1 halpha
  exact ⟨n, by
    simpa only [veblenSuccSequence, eval_veblenIterate] using hn⟩

/-- Certified sequence at a successor argument of a successor Veblen index. -/
def veblenSuccLimitSequenceData {index lower arg beta : G0}
    (hi : predecessor? index = some lower)
    (ha : predecessor? arg = some beta) : LimitSequenceData (veblen index arg) where
  seq := veblenSuccSequence lower index beta
  isSuccLimit := by
    rw [eval_veblen]
    exact isSuccLimit_veblen_of_index_pos (eval arg)
      (lt_of_le_of_lt zero_le ((lt_iff_eval_lt _ _).1 (predecessor?_lt hi)))
  strictMono := veblenSuccSequence_strictMono hi beta
  lt := veblenSuccSequence_lt hi ha
  cofinal := veblenSuccSequence_cofinal hi ha

@[simp]
theorem veblenSuccLimitSequenceData_seq {index lower arg beta : G0}
    (hi : predecessor? index = some lower)
    (ha : predecessor? arg = some beta) (n : Nat) :
    (veblenSuccLimitSequenceData hi ha).seq n =
      veblenSuccSequence lower index beta n := rfl

theorem veblenSuccSequence_iSup_eval {index lower arg beta : G0}
    (hi : predecessor? index = some lower)
    (ha : predecessor? arg = some beta) :
    (⨆ n, eval (veblenSuccSequence lower index beta n)) =
      eval (veblen index arg) := by
  have h := (veblenSuccLimitSequenceData hi ha).iSup_eval
  simpa only [veblenSuccLimitSequenceData_seq] using h

end G0
end OrdinalAnalysis
