import OrdinalAnalysis.Gamma0.VeblenApplication
import OrdinalAnalysis.Gamma0.SemanticNormalForm

/-!
# Finite multiples of canonical Veblen principal values

A normal term whose value is a power of ω has the same value as its leading
principal term. This lets an executable constructor replace that principal's
coefficient, including after a Veblen fixed-point collapse.
-/

namespace OrdinalAnalysis
namespace G0Term

open Ordinal Order

/-- A normal additive principal value equals the value of its leading principal term. -/
theorem eval_eq_leading_principal_of_opow
    {index arg tail : G0Term} {coeff : Nat}
    (hn : IsNormal (.veblen index arg coeff tail))
    (hpower : ∃ y : Ordinal.{0}, eval (.veblen index arg coeff tail) = ω ^ y) :
    eval (.veblen index arg coeff tail) = eval (principal index arg) := by
  obtain ⟨y, hy⟩ := hpower
  obtain ⟨x, hx⟩ := Ordinal.veblen_mem_range_opow (eval index) (eval arg)
  have htail : eval tail < ω ^ x := by
    simpa only [eval_principal, hx] using
      (hasSemanticTailBounds_of_normal _ hn).tail_lt_principal
  have hupper : eval (.veblen index arg coeff tail) < ω ^ (x + 1) := by
    rw [eval_veblen, ← hx]
    exact Ordinal.opow_mul_add_lt_opow (Ordinal.natCast_lt_omega0 coeff.succ)
      htail (lt_add_one x)
  have hyx : y < x + 1 := by
    apply (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).1
    simpa only [hy] using hupper
  apply le_antisymm
  · calc
      eval (.veblen index arg coeff tail) = ω ^ y := hy
      _ ≤ ω ^ x :=
        (Ordinal.opow_le_opow_iff_right Ordinal.one_lt_omega0).2
          (lt_add_one_iff.1 hyx)
      _ = eval (principal index arg) := by
        simpa only [eval_principal] using hx
  · exact eval_principal_le_eval_veblen index arg coeff tail

/--
Replace the leading coefficient by a natural multiplier. Its multiplication
specification is used only when the input has an additive principal value.
-/
def principalMulNatRaw : G0Term → Nat → G0Term
  | _, 0 => .zero
  | .zero, _ + 1 => .zero
  | .veblen index arg _ _, n + 1 => .veblen index arg n .zero

theorem isNormal_principalMulNatRaw {t : G0Term} (hn : IsNormal t) (n : Nat) :
    IsNormal (principalMulNatRaw t n) := by
  cases n with
  | zero => exact isNormal_zero
  | succ n =>
      cases t with
      | zero => exact isNormal_zero
      | veblen index arg coeff tail =>
          exact (isNormal_veblen_zero_iff index arg n).2
            ⟨hn.index, hn.arg, hn.arg_lt_principal⟩

/-- On normal principal-valued inputs, the executable coefficient replacement is multiplication. -/
theorem eval_principalMulNatRaw {t : G0Term}
    (hn : IsNormal t) (hpower : ∃ y : Ordinal.{0}, eval t = ω ^ y) (n : Nat) :
    eval (principalMulNatRaw t n) = eval t * (n : Ordinal.{0}) := by
  cases n with
  | zero =>
      simp [principalMulNatRaw]
  | succ n =>
      cases t with
      | zero =>
          simp [principalMulNatRaw]
      | veblen index arg coeff tail =>
          have heq := eval_eq_leading_principal_of_opow hn hpower
          change Ordinal.veblen (eval index) (eval arg) * (n.succ : Ordinal.{0}) + 0 =
            eval (.veblen index arg coeff tail) * (n.succ : Ordinal.{0})
          rw [add_zero, heq, eval_principal]

end G0Term

namespace G0

open Ordinal

/-- Executable finite right multiplication of a canonical Veblen value. -/
def veblenMulNat (index arg : G0) (n : Nat) : G0 :=
  ⟨G0Term.principalMulNatRaw (veblen index arg).1 n,
    G0Term.isNormal_principalMulNatRaw (veblen index arg).2 n⟩

@[simp]
theorem eval_veblenMulNat (index arg : G0) (n : Nat) :
    eval (veblenMulNat index arg n) =
      Ordinal.veblen (eval index) (eval arg) * (n : Ordinal.{0}) := by
  have hpower : ∃ y : Ordinal.{0}, G0Term.eval (veblen index arg).1 = ω ^ y := by
    obtain ⟨y, hy⟩ := Ordinal.veblen_mem_range_opow (eval index) (eval arg)
    exact ⟨y, (eval_veblen index arg).trans hy.symm⟩
  calc
    eval (veblenMulNat index arg n) =
        eval (veblen index arg) * (n : Ordinal.{0}) :=
      G0Term.eval_principalMulNatRaw (veblen index arg).2 hpower n
    _ = Ordinal.veblen (eval index) (eval arg) * (n : Ordinal.{0}) := by
      rw [eval_veblen]

end G0
end OrdinalAnalysis
