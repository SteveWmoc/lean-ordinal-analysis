import OrdinalAnalysis.Gamma0.Uniqueness
import OrdinalAnalysis.Gamma0.LinearOrder

/-!
# Executable canonical Veblen application

A principal expression φ_index(arg) is already canonical when its argument is
strictly smaller than its value. Otherwise normal inputs force a fixed-point
collapse, so the existing canonical argument is the correct result.

The decision uses the raw comparator. Ordinal evaluation is used only in the
correctness proof, never in the computation.
-/

namespace OrdinalAnalysis
namespace G0Term

open Ordinal

/-- Form a principal term, collapsing a redundant fixed-point presentation. -/
def principalNF (index arg : G0Term) : G0Term :=
  if compareRaw arg (principal index arg) = .lt then principal index arg else arg

/-- Canonical inputs give a canonical principal result. -/
theorem isNormal_principalNF {index arg : G0Term}
    (hindex : IsNormal index) (harg : IsNormal arg) :
    IsNormal (principalNF index arg) := by
  unfold principalNF
  split
  next h => exact IsNormal.principal hindex harg h
  next => exact harg

/-- The executable fixed-point collapse preserves Veblen evaluation. -/
theorem eval_principalNF {index arg : G0Term}
    (hindex : IsNormal index) (harg : IsNormal arg) :
    eval (principalNF index arg) = Ordinal.veblen (eval index) (eval arg) := by
  unfold principalNF
  split
  next =>
    exact eval_principal index arg
  next h =>
    have hcmp := compareRaw_eq_cmp_eval arg (principal index arg)
      (hasSemanticTailBounds_of_normal arg harg)
      (HasSemanticTailBounds.principal
        (hasSemanticTailBounds_of_normal index hindex)
        (hasSemanticTailBounds_of_normal arg harg))
    have hnot : ¬ eval arg < eval (principal index arg) := by
      intro hlt
      apply h
      rw [hcmp]
      exact (cmp_eq_lt_iff _ _).2 hlt
    have hle : eval arg ≤ eval (principal index arg) := by
      simpa only [eval_principal] using Ordinal.right_le_veblen (eval index) (eval arg)
    exact (le_antisymm hle (le_of_not_gt hnot)).trans (eval_principal index arg)

end G0Term

namespace G0

open Ordinal

/-- Executable Veblen application on canonical Γ₀ notations. -/
def veblen (index arg : G0) : G0 :=
  ⟨G0Term.principalNF index.1 arg.1, G0Term.isNormal_principalNF index.2 arg.2⟩

/-- Canonical application agrees exactly with mathlib's Veblen hierarchy. -/
@[simp]
theorem eval_veblen (index arg : G0) :
    eval (veblen index arg) = Ordinal.veblen (eval index) (eval arg) :=
  G0Term.eval_principalNF index.2 arg.2

/-- At a fixed index, canonical Veblen application is strictly monotone. -/
theorem veblen_right_strictMono (index : G0) : StrictMono (veblen index) := by
  intro a b hab
  apply (lt_iff_eval_lt _ _).2
  rw [eval_veblen, eval_veblen]
  exact Ordinal.veblen_right_strictMono (eval index) ((lt_iff_eval_lt a b).1 hab)

end G0
end OrdinalAnalysis
