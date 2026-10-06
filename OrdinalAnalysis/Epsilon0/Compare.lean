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
Raw comparison is reversed by swapping its arguments.
-/
@[simp]
theorem compareRaw_swap : ∀ a b : E0Term, (compareRaw a b).swap = compareRaw b a := by
  intro a
  induction a with
  | zero =>
      intro b
      cases b <;> rfl
  | cnf exp coeff tail ihExp ihTail =>
      intro b
      cases b with
      | zero =>
          rfl
      | cnf exp' coeff' tail' =>
          rw [compareRaw, compareRaw, ← ihExp exp', ← Nat.compare_swap coeff coeff']
          cases hExp : compareRaw exp exp' with
          | lt =>
              simp [hExp, Ordering.swap]
          | gt =>
              simp [hExp, Ordering.swap]
          | eq =>
              cases hCoeff : compare coeff coeff' with
              | lt =>
                  simp [hExp, hCoeff, Ordering.swap]
              | gt =>
                  simp [hExp, hCoeff, Ordering.swap]
              | eq =>
                  simp [hExp, hCoeff, ihTail tail', Ordering.swap]

/--
The proposition that one raw ε₀ term is syntactically smaller than another.

We deliberately do not install this as the global `LT E0Term` instance:
the raw datatype contains noncanonical terms.  The eventual canonical subtype
will receive the notation-system order.
-/
def RawLT (a b : E0Term) : Prop :=
  compareRaw a b = .lt

/-- A raw `.gt` result is exactly strict raw comparison in the reverse direction. -/
@[simp]
theorem compareRaw_eq_gt_iff_reverse_rawLT (a b : E0Term) :
    compareRaw a b = .gt ↔ RawLT b a := by
  rw [RawLT, ← compareRaw_swap a b]
  cases h : compareRaw a b <;> simp [h, Ordering.swap]

/-- Boolean form of raw syntactic strict comparison. -/
def rawLT (a b : E0Term) : Bool :=
  compareRaw a b == .lt

@[simp]
theorem not_rawLT_self (a : E0Term) : ¬ RawLT a a := by
  simp [RawLT]

/-- Zero is raw-smaller than every nonzero raw term. -/
@[simp]
theorem rawLT_zero_cnf (exp : E0Term) (coeff : Nat) (tail : E0Term) :
    RawLT .zero (.cnf exp coeff tail) :=
  rfl

/-- No nonzero raw term is raw-smaller than zero. -/
@[simp]
theorem not_rawLT_cnf_zero (exp : E0Term) (coeff : Nat) (tail : E0Term) :
    ¬ RawLT (.cnf exp coeff tail) .zero := by
  simp [RawLT, compareRaw]

/--
Lexicographic characterization of strict raw comparison between two CNF nodes.

A node is smaller precisely when its exponent is smaller, or the exponents are
equal and its coefficient is smaller, or both exponent and coefficient are
equal and its tail is smaller.
-/
theorem rawLT_cnf_iff
    (exp exp' : E0Term) (coeff coeff' : Nat) (tail tail' : E0Term) :
    RawLT (.cnf exp coeff tail) (.cnf exp' coeff' tail') ↔
      RawLT exp exp' ∨
      (exp = exp' ∧
        (coeff < coeff' ∨
          (coeff = coeff' ∧ RawLT tail tail'))) := by
  cases hExp : compareRaw exp exp' with
  | lt =>
      simp [RawLT, compareRaw, hExp]
  | gt =>
      have hne : exp ≠ exp' := by
        intro he
        have heq : compareRaw exp exp' = .eq :=
          (compareRaw_eq_eq_iff exp exp').2 he
        rw [hExp] at heq
        contradiction
      simp [RawLT, compareRaw, hExp, hne]
  | eq =>
      have he : exp = exp' :=
        (compareRaw_eq_eq_iff exp exp').1 hExp
      subst exp'
      cases hCoeff : compare coeff coeff' with
      | lt =>
          have hc : coeff < coeff' :=
            Nat.compare_eq_lt.mp hCoeff
          simp [RawLT, compareRaw, compareRaw_self, hCoeff, hc]
      | gt =>
          have hc : coeff' < coeff :=
            Nat.compare_eq_gt.mp hCoeff
          have hnotlt : ¬ coeff < coeff' :=
            Nat.lt_asymm hc
          have hne : coeff ≠ coeff' := by
            intro heq
            subst coeff'
            exact (Nat.lt_irrefl coeff) hc
          simp [RawLT, compareRaw, compareRaw_self, hCoeff, hnotlt, hne]
      | eq =>
          have hc : coeff = coeff' :=
            Nat.compare_eq_eq.mp hCoeff
          subst coeff'
          simp [RawLT, compareRaw, compareRaw_self, hCoeff]

example : compareRaw E0Term.zero E0Term.zero = .eq := rfl
example : compareRaw E0Term.zero E0Term.one = .lt := rfl
example : compareRaw E0Term.one E0Term.zero = .gt := rfl
example : compareRaw E0Term.one E0Term.one = .eq := rfl
example : RawLT E0Term.zero E0Term.one := rfl
example : rawLT E0Term.zero E0Term.one = true := rfl

end E0Term
end OrdinalAnalysis
