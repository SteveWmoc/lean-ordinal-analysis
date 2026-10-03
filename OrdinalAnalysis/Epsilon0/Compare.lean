import OrdinalAnalysis.Epsilon0.Term

/-!
# Raw comparison for ε₀ terms

This file defines the executable lexicographic comparison used by the ε₀
notation system.

The comparison is purely syntactic.  It does not interpret terms as mathlib
ordinals and it does not assume that the inputs are in Cantor normal form.

For nonzero raw terms

```
ω ^ α * m + β
ω ^ γ * n + δ
```

comparison proceeds lexicographically:

1. compare the exponents `α` and `γ`;
2. if they are equal, compare the stored coefficients;
3. if those are equal, compare the tails `β` and `δ`.

Because the stored coefficient is one less than the mathematical positive
coefficient, comparing stored coefficients gives the same result as comparing
the represented coefficients.
-/

namespace OrdinalAnalysis
namespace E0Term

/--
Executable lexicographic comparison of raw ε₀ terms.

This function is structural and independent of `Ordinal`.  Later we will
prove that, on canonical terms, it agrees with semantic ordinal comparison.
-/
def compareRaw : E0Term → E0Term → Ordering
  | .zero, .zero => .eq
  | .zero, .cnf _ _ _ => .lt
  | .cnf _ _ _, .zero => .gt
  | .cnf exp coeff tail, .cnf exp' coeff' tail' =>
      match compareRaw exp exp' with
      | .lt => .lt
      | .gt => .gt
      | .eq =>
          match compare coeff coeff' with
          | .lt => .lt
          | .gt => .gt
          | .eq => compareRaw tail tail'

/-- Raw comparison is reflexive at `Ordering.eq`. -/
@[simp]
theorem compareRaw_self : ∀ a : E0Term, compareRaw a a = .eq
  | .zero => rfl
  | .cnf exp coeff tail => by
      rw [compareRaw, compareRaw_self exp]
      have hcoeff : compare coeff coeff = .eq :=
        Nat.compare_eq_eq.mpr rfl
      rw [hcoeff]
      exact compareRaw_self tail

/--
Raw comparison returns `Ordering.eq` exactly for syntactically equal terms.

This is a purely syntactic certification lemma.  It does not require
canonicality or ordinal semantics.
-/
@[simp]
theorem compareRaw_eq_eq_iff : ∀ a b : E0Term, compareRaw a b = .eq ↔ a = b := by
  intro a
  induction a with
  | zero =>
      intro b
      cases b <;> simp [compareRaw]
  | cnf exp coeff tail ihExp ihTail =>
      intro b
      cases b with
      | zero =>
          simp [compareRaw]
      | cnf exp' coeff' tail' =>
          rw [compareRaw]
          cases hExp : compareRaw exp exp' with
          | lt =>
              have hne : exp ≠ exp' := by
                intro he
                have heq : compareRaw exp exp' = .eq :=
                  (ihExp exp').2 he
                rw [hExp] at heq
                contradiction
              simp [hExp, hne]
          | gt =>
              have hne : exp ≠ exp' := by
                intro he
                have heq : compareRaw exp exp' = .eq :=
                  (ihExp exp').2 he
                rw [hExp] at heq
                contradiction
              simp [hExp, hne]
          | eq =>
              have he : exp = exp' :=
                (ihExp exp').1 hExp
              subst exp'
              cases hCoeff : compare coeff coeff' with
              | lt =>
                  have hne : coeff ≠ coeff' := by
                    intro hc
                    subst coeff'
                    have heq : compare coeff coeff = .eq :=
                      Nat.compare_eq_eq.mpr rfl
                    rw [heq] at hCoeff
                    contradiction
                  simp [hExp, hCoeff, hne]
              | gt =>
                  have hne : coeff ≠ coeff' := by
                    intro hc
                    subst coeff'
                    have heq : compare coeff coeff = .eq :=
                      Nat.compare_eq_eq.mpr rfl
                    rw [heq] at hCoeff
                    contradiction
                  simp [hExp, hCoeff, hne]
              | eq =>
                  have hc : coeff = coeff' :=
                    Nat.compare_eq_eq.mp hCoeff
                  subst coeff'
                  simp [hExp, hCoeff, ihTail]

/--
The proposition that one raw ε₀ term is syntactically smaller than another.

We deliberately do not install this as the global `LT E0Term` instance:
the raw datatype contains noncanonical terms.  The eventual canonical subtype
will receive the notation-system order.
-/
def RawLT (a b : E0Term) : Prop :=
  compareRaw a b = .lt

/-- Boolean form of raw syntactic strict comparison. -/
def rawLT (a b : E0Term) : Bool :=
  compareRaw a b == .lt

@[simp]
theorem not_rawLT_self (a : E0Term) : ¬ RawLT a a := by
  simp [RawLT]

example : compareRaw E0Term.zero E0Term.zero = .eq := rfl
example : compareRaw E0Term.zero E0Term.one = .lt := rfl
example : compareRaw E0Term.one E0Term.zero = .gt := rfl
example : compareRaw E0Term.one E0Term.one = .eq := rfl
example : RawLT E0Term.zero E0Term.one := rfl
example : rawLT E0Term.zero E0Term.one = true := rfl

end E0Term
end OrdinalAnalysis
