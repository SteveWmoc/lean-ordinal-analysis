import OrdinalAnalysis.Gamma0.Semantics

/-!
# Semantic comparison infrastructure for Γ₀ terms

This file isolates the ordinal arithmetic needed to certify the executable
Veblen comparator.

The key auxiliary invariant, `HasSemanticTailBounds`, says recursively that
every tail lies below the Veblen principal term leading its node. Comparator
correctness is first proved under this semantic invariant. A later theorem
shows that executable Veblen normality implies the invariant, breaking the
otherwise circular dependency between tail bounds and comparison soundness.
-/

namespace OrdinalAnalysis
namespace G0Term

open Ordinal

/--
Every recursive tail in a raw Γ₀ term lies semantically below its own leading
Veblen principal term.
-/
def HasSemanticTailBounds : G0Term → Prop
  | .zero => True
  | .veblen index arg _ tail =>
      HasSemanticTailBounds index ∧
      HasSemanticTailBounds arg ∧
      HasSemanticTailBounds tail ∧
      eval tail < eval (principal index arg)

namespace HasSemanticTailBounds

@[simp]
theorem zero : HasSemanticTailBounds G0Term.zero :=
  trivial

theorem index
    {index arg : G0Term} {coeff : Nat} {tail : G0Term}
    (h : HasSemanticTailBounds (.veblen index arg coeff tail)) :
    HasSemanticTailBounds index :=
  h.1

theorem arg
    {index arg : G0Term} {coeff : Nat} {tail : G0Term}
    (h : HasSemanticTailBounds (.veblen index arg coeff tail)) :
    HasSemanticTailBounds arg :=
  h.2.1

theorem tail
    {index arg : G0Term} {coeff : Nat} {tail : G0Term}
    (h : HasSemanticTailBounds (.veblen index arg coeff tail)) :
    HasSemanticTailBounds tail :=
  h.2.2.1

theorem tail_lt_principal
    {index arg : G0Term} {coeff : Nat} {tail : G0Term}
    (h : HasSemanticTailBounds (.veblen index arg coeff tail)) :
    eval tail < eval (principal index arg) :=
  h.2.2.2

/-- Principal terms inherit the semantic-tail invariant from their two parameters. -/
theorem principal
    {index arg : G0Term}
    (hindex : HasSemanticTailBounds index)
    (harg : HasSemanticTailBounds arg) :
    HasSemanticTailBounds (G0Term.principal index arg) := by
  change
    HasSemanticTailBounds index ∧
      HasSemanticTailBounds arg ∧
      HasSemanticTailBounds G0Term.zero ∧
      eval G0Term.zero < eval (G0Term.principal index arg)
  exact ⟨hindex, harg, trivial, by simp⟩

end HasSemanticTailBounds

/-- Every nonzero Γ₀ constructor has positive semantic value. -/
theorem eval_veblen_pos
    (index arg : G0Term) (coeff : Nat) (tail : G0Term) :
    0 < eval (.veblen index arg coeff tail) := by
  rw [eval_veblen]
  rcases Ordinal.veblen_mem_range_opow (eval index) (eval arg) with ⟨x, hx⟩
  rw [← hx]
  exact
    Ordinal.opow_mul_add_pos Ordinal.omega0_ne_zero x
      (by simp) (eval tail)

/-- The leading Veblen block is bounded by the value of the whole node. -/
theorem leadingBlock_le_eval
    (index arg : G0Term) (coeff : Nat) (tail : G0Term) :
    Ordinal.veblen (eval index) (eval arg) *
        (coeff.succ : Ordinal.{0}) ≤
      eval (.veblen index arg coeff tail) := by
  rw [eval_veblen]
  exact le_self_add

/--
If the source tail lies below its leading Veblen principal and that principal
is strictly below another Veblen principal, then the whole source node lies
below the larger principal.
-/
theorem eval_veblen_lt_principal_of_principal_lt
    {index arg tail index' arg' : G0Term} (coeff : Nat)
    (htail :
      eval tail < eval (principal index arg))
    (hprincipal :
      Ordinal.veblen (eval index) (eval arg) <
        Ordinal.veblen (eval index') (eval arg')) :
    eval (.veblen index arg coeff tail) <
      Ordinal.veblen (eval index') (eval arg') := by
  rcases Ordinal.veblen_mem_range_opow (eval index) (eval arg) with ⟨x, hx⟩
  rcases Ordinal.veblen_mem_range_opow (eval index') (eval arg') with ⟨y, hy⟩
  have hxy : x < y := by
    apply (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).1
    simpa [hx, hy] using hprincipal
  rw [eval_veblen, ← hx, ← hy]
  apply Ordinal.opow_mul_add_lt_opow
  · exact Ordinal.natCast_lt_omega0 coeff.succ
  · simpa [eval_principal, hx] using htail
  · exact hxy

/-- A smaller leading Veblen principal makes the whole source node smaller. -/
theorem eval_veblen_lt_of_principal_lt
    {index arg tail index' arg' tail' : G0Term}
    (coeff coeff' : Nat)
    (htail :
      eval tail < eval (principal index arg))
    (hprincipal :
      Ordinal.veblen (eval index) (eval arg) <
        Ordinal.veblen (eval index') (eval arg')) :
    eval (.veblen index arg coeff tail) <
      eval (.veblen index' arg' coeff' tail') := by
  have hsource :=
    eval_veblen_lt_principal_of_principal_lt coeff htail hprincipal
  have hcoeffPos : 0 < (coeff'.succ : Ordinal.{0}) := by simp
  have hprincipal_le :
      Ordinal.veblen (eval index') (eval arg') ≤
        Ordinal.veblen (eval index') (eval arg') *
          (coeff'.succ : Ordinal.{0}) :=
    Ordinal.le_mul_left _ hcoeffPos
  exact
    hsource.trans_le
      (hprincipal_le.trans
        (leadingBlock_le_eval index' arg' coeff' tail'))

/-- At a common principal term, a smaller finite coefficient wins. -/
theorem eval_veblen_lt_of_coeff_lt
    {index arg tail tail' : G0Term} {coeff coeff' : Nat}
    (htail :
      eval tail < eval (principal index arg))
    (hcoeff : coeff < coeff') :
    eval (.veblen index arg coeff tail) <
      eval (.veblen index arg coeff' tail') := by
  rcases Ordinal.veblen_mem_range_opow (eval index) (eval arg) with ⟨x, hx⟩
  rw [eval_veblen, eval_veblen, ← hx]
  have hcoeff' :
      (coeff.succ : Ordinal.{0}) < (coeff'.succ : Ordinal.{0}) := by
    exact_mod_cast Nat.succ_lt_succ hcoeff
  exact
    (Ordinal.opow_mul_add_lt_opow_mul
      (by simpa [eval_principal, hx] using htail) hcoeff').trans_le le_self_add

/--
At semantically equal Veblen principal terms, a smaller finite coefficient
makes the whole source node smaller.
-/
theorem eval_veblen_lt_of_coeff_lt_of_principal_eq
    {index arg tail index' arg' tail' : G0Term}
    {coeff coeff' : Nat}
    (htail :
      eval tail < eval (principal index arg))
    (hprincipal :
      Ordinal.veblen (eval index) (eval arg) =
        Ordinal.veblen (eval index') (eval arg'))
    (hcoeff : coeff < coeff') :
    eval (.veblen index arg coeff tail) <
      eval (.veblen index' arg' coeff' tail') := by
  rcases Ordinal.veblen_mem_range_opow (eval index) (eval arg) with ⟨x, hx⟩
  rw [eval_veblen, eval_veblen, ← hprincipal, ← hx]
  have hcoeff' :
      (coeff.succ : Ordinal.{0}) < (coeff'.succ : Ordinal.{0}) := by
    exact_mod_cast Nat.succ_lt_succ hcoeff
  exact
    (Ordinal.opow_mul_add_lt_opow_mul
      (by simpa [eval_principal, hx] using htail) hcoeff').trans_le le_self_add

/--
At semantically equal Veblen principal terms and a common coefficient,
comparison reduces to the tails.
-/
theorem eval_veblen_lt_of_tail_lt_of_principal_eq
    {index arg tail index' arg' tail' : G0Term}
    {coeff : Nat}
    (hprincipal :
      Ordinal.veblen (eval index) (eval arg) =
        Ordinal.veblen (eval index') (eval arg'))
    (htail : eval tail < eval tail') :
    eval (.veblen index arg coeff tail) <
      eval (.veblen index' arg' coeff tail') := by
  rw [eval_veblen, eval_veblen, ← hprincipal]
  exact (add_lt_add_iff_left _).2 htail

/-- At a common principal term and coefficient, comparison reduces to the tails. -/
theorem eval_veblen_lt_of_tail_lt
    {index arg tail tail' : G0Term} {coeff : Nat}
    (htail : eval tail < eval tail') :
    eval (.veblen index arg coeff tail) <
      eval (.veblen index arg coeff tail') := by
  rw [eval_veblen, eval_veblen]
  exact (add_lt_add_iff_left _).2 htail

end G0Term
end OrdinalAnalysis
