import OrdinalAnalysis.Gamma0.Predecessor

/-!
# Executable successors of canonical Γ₀ notations

Increment a final finite block, or append one at the rightmost limit block.
Normality and successor evaluation are proved together by recursion on syntax.
-/

namespace OrdinalAnalysis
namespace G0Term

open Ordinal Order

/-- Compute successor syntax by following the rightmost tail. -/
def successor : G0Term → G0Term
  | .zero => one
  | .veblen .zero .zero coeff _ => .veblen .zero .zero (coeff + 1) .zero
  | .veblen index arg coeff tail => .veblen index arg coeff (successor tail)

private theorem successor_node_correct
    {index arg tail : G0Term} {coeff : Nat}
    (hn : IsNormal (.veblen index arg coeff tail))
    (hlimit : IsSuccLimit (Ordinal.veblen (eval index) (eval arg)))
    (ih : IsNormal (successor tail) ∧
      eval (successor tail) = Order.succ (eval tail)) :
    IsNormal (.veblen index arg coeff (successor tail)) ∧
      eval (.veblen index arg coeff (successor tail)) =
        Order.succ (eval (.veblen index arg coeff tail)) := by
  constructor
  · apply isNormal_veblen_of_eval_bounds coeff hn.index hn.arg ih.1
    · have hraw := (rawLT_iff_eval_lt arg (principal index arg)
        hn.arg (IsNormal.principal hn.index hn.arg hn.arg_lt_principal)).1
        hn.arg_lt_principal
      simpa only [eval_principal] using hraw
    · rw [ih.2]
      apply hlimit.succ_lt
      simpa only [eval_principal] using
        (hasSemanticTailBounds_of_normal _ hn).tail_lt_principal
  · rw [eval_veblen, ih.2, eval_veblen]
    simp only [Order.succ_eq_add_one, add_assoc]

/-- Successor computation preserves normality and has the expected ordinal value. -/
theorem successor_correct (t : G0Term) (hn : IsNormal t) :
    IsNormal (successor t) ∧ eval (successor t) = Order.succ (eval t) := by
  induction t with
  | zero =>
      constructor
      · native_decide
      · simp [successor, Order.succ_eq_add_one]
  | veblen index arg coeff tail _ _ ihTail =>
      cases index with
      | zero =>
          cases arg with
          | zero =>
              have ht : eval tail = 0 := by
                have hb := (hasSemanticTailBounds_of_normal _ hn).tail_lt_principal
                simpa [eval_principal, Ordinal.veblen_zero_apply] using hb
              constructor
              · simp [successor, principal]
              · simp [successor, eval_veblen, Ordinal.veblen_zero_apply, ht,
                  Order.succ_eq_add_one, Nat.cast_add_one]
          | veblen ai aa ac argTail =>
              have hl := terminalSuccessorView_satisfies .zero (.veblen ai aa ac argTail) 0
              have hlimit : IsSuccLimit (Ordinal.veblen (eval .zero)
                  (eval (.veblen ai aa ac argTail))) := by
                simpa [terminalSuccessorView, SuccessorView.Satisfies, eval_veblen]
                  using hl
              exact successor_node_correct hn hlimit (ihTail hn.tail)
      | veblen ii ia ic it =>
          have hl := terminalSuccessorView_satisfies (.veblen ii ia ic it) arg 0
          have hlimit : IsSuccLimit
              (Ordinal.veblen (eval (.veblen ii ia ic it)) (eval arg)) := by
            simpa [terminalSuccessorView, SuccessorView.Satisfies, eval_veblen]
              using hl
          exact successor_node_correct hn hlimit (ihTail hn.tail)

end G0Term

namespace G0

open Ordinal Order

/-- Executable canonical successor. -/
def successor (a : G0) : G0 :=
  ⟨G0Term.successor a.1, (G0Term.successor_correct a.1 a.2).1⟩

@[simp]
theorem eval_successor (a : G0) :
    eval (successor a) = Order.succ (eval a) :=
  (G0Term.successor_correct a.1 a.2).2

theorem lt_successor (a : G0) : a < successor a := by
  apply (lt_iff_eval_lt _ _).2
  rw [eval_successor]
  exact lt_succ _

end G0
end OrdinalAnalysis
