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

example : compareRaw E0Term.zero E0Term.zero = .eq := rfl
example : compareRaw E0Term.zero E0Term.one = .lt := rfl
example : compareRaw E0Term.one E0Term.zero = .gt := rfl
example : compareRaw E0Term.one E0Term.one = .eq := rfl
example : RawLT E0Term.zero E0Term.one := rfl
example : rawLT E0Term.zero E0Term.one = true := rfl

end E0Term
end OrdinalAnalysis
