import OrdinalAnalysis.Gamma0.Uniqueness

/-!
# Constructing normal Γ₀ nodes from semantic bounds

The completeness proof receives ordinal inequalities from its decomposition.
This file converts those inequalities into the executable comparisons required
by normality. Comparison with a newly formed principal term first uses the
semantic-tail invariant, avoiding any assumption that it is already normal.
-/

namespace OrdinalAnalysis
namespace G0Term

open Ordinal

/-- The leading principal term is bounded by the value of any nonzero node. -/
theorem eval_principal_le_eval_veblen
    (index arg : G0Term) (coeff : Nat) (tail : G0Term) :
    eval (principal index arg) ≤ eval (.veblen index arg coeff tail) := by
  rw [eval_principal]
  exact (Ordinal.le_mul_left _ (show 0 < (coeff.succ : Ordinal.{0}) by simp)).trans
    (leadingBlock_le_eval index arg coeff tail)

/--
Normal inputs form a normal node when its argument and whole tail lie below
its leading principal value.
-/
theorem isNormal_veblen_of_eval_bounds
    {index arg tail : G0Term} (coeff : Nat)
    (hindex : IsNormal index) (harg : IsNormal arg) (htail : IsNormal tail)
    (hargLt : eval arg < Ordinal.veblen (eval index) (eval arg))
    (htailLt : eval tail < Ordinal.veblen (eval index) (eval arg)) :
    IsNormal (.veblen index arg coeff tail) := by
  have hprincipalBounds : HasSemanticTailBounds (principal index arg) :=
    HasSemanticTailBounds.principal
      (hasSemanticTailBounds_of_normal index hindex)
      (hasSemanticTailBounds_of_normal arg harg)
  have hargRaw : RawLT arg (principal index arg) := by
    rw [RawLT, compareRaw_eq_cmp_eval arg (principal index arg)
      (hasSemanticTailBounds_of_normal arg harg) hprincipalBounds]
    apply (cmp_eq_lt_iff _ _).2
    simpa only [eval_principal] using hargLt
  have hprincipalNormal : IsNormal (principal index arg) :=
    IsNormal.principal hindex harg hargRaw
  apply (isNormal_veblen_iff index arg coeff tail).2
  refine ⟨hindex, harg, htail, hargRaw, ?_⟩
  cases tail with
  | zero =>
      trivial
  | veblen tailIndex tailArg tailCoeff tailTail =>
      apply (rawLT_iff_eval_lt
        (principal tailIndex tailArg) (principal index arg)
        (IsNormal.principal htail.index htail.arg htail.arg_lt_principal)
        hprincipalNormal).2
      have hle := eval_principal_le_eval_veblen
        tailIndex tailArg tailCoeff tailTail
      exact hle.trans_lt (by simpa only [eval_principal] using htailLt)

end G0Term
end OrdinalAnalysis
