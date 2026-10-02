import OrdinalAnalysis.Epsilon0.Semantics

/-!
# Semantic bounds for ε₀ terms

This file records elementary ordinal bounds for one Cantor-normal-form node.
They are deliberately stated without assuming global comparison correctness.

The key lemma says that if the tail already lies below the leading power of
`ω`, then the whole CNF node lies below every strictly larger power of `ω`.
This is the non-circular ingredient needed by the later induction proving that
syntactic comparison agrees with ordinal comparison.
-/

namespace OrdinalAnalysis
namespace E0Term

/-- Every nonzero CNF constructor has positive ordinal value. -/
theorem eval_cnf_pos (exp : E0Term) (coeff : Nat) (tail : E0Term) :
    0 < eval (.cnf exp coeff tail) := by
  rw [eval_cnf]
  exact
    Ordinal.opow_mul_add_pos Ordinal.omega0_ne_zero (eval exp)
      (by simp) (eval tail)

/-- The leading Cantor block is bounded above by the value of the whole node. -/
theorem leadingBlock_le_eval (exp : E0Term) (coeff : Nat) (tail : E0Term) :
    Ordinal.omega0 ^ eval exp * (coeff.succ : Ordinal) ≤
      eval (.cnf exp coeff tail) := by
  rw [eval_cnf]
  exact le_self_add

/--
If the tail is below the leading power of `ω`, then the whole CNF node is
below any strictly larger power of `ω`.
-/
theorem eval_cnf_lt_opow_of_tail_lt
    {exp tail : E0Term} (coeff : Nat) {x : Ordinal}
    (htail : eval tail < Ordinal.omega0 ^ eval exp)
    (hexp : eval exp < x) :
    eval (.cnf exp coeff tail) < Ordinal.omega0 ^ x := by
  rw [eval_cnf]
  have hcoeff :
      (coeff.succ : Ordinal) < (Ordinal.omega0 : Ordinal) :=
    Ordinal.natCast_lt_omega0 coeff.succ
  exact
    Ordinal.opow_mul_add_lt_opow hcoeff htail hexp

/--
A convenient successor-exponent specialization of
`eval_cnf_lt_opow_of_tail_lt`.
-/
theorem eval_cnf_lt_nextPower_of_tail_lt
    {exp tail : E0Term} (coeff : Nat)
    (htail : eval tail < Ordinal.omega0 ^ eval exp) :
    eval (.cnf exp coeff tail) <
      Ordinal.omega0 ^ (eval exp + 1) := by
  exact eval_cnf_lt_opow_of_tail_lt coeff htail (lt_add_one _)

end E0Term
end OrdinalAnalysis
