import OrdinalAnalysis.Epsilon0.Compare

/-!
# Cantor normal form below ε₀

This file separates canonical ordinal notations from the raw recursive syntax.

The executable predicate `isNormal` checks that exponents and tails are
themselves normal and that the leading exponent of each nonzero tail is
strictly smaller than the current leading exponent.  The proposition
`IsNormal` packages that Boolean check for use in theorem statements.

The canonical notation type `E0` is the subtype of raw terms satisfying this
predicate.
-/

namespace OrdinalAnalysis
namespace E0Term

/--
Executable Cantor-normal-form check for raw ε₀ terms.

A term `cnf exp coeff tail` is normal when

* `exp` is normal;
* `tail` is normal; and
* if `tail` is nonzero, its leading exponent is strictly smaller than `exp`.

The coefficient requires no extra condition because the raw constructor stores
one less than the mathematical coefficient, so every represented coefficient
is automatically positive.
-/
def isNormal : E0Term → Bool
  | .zero => true
  | .cnf exp _ tail =>
      isNormal exp &&
      isNormal tail &&
      match tail with
      | .zero => true
      | .cnf tailExp _ _ => rawLT tailExp exp

/-- A raw ε₀ term is canonical exactly when the executable normal-form check succeeds. -/
def IsNormal (t : E0Term) : Prop :=
  t.isNormal = true

instance instDecidableIsNormal (t : E0Term) : Decidable t.IsNormal := by
  unfold IsNormal
  exact decEq t.isNormal true

/--
A simple noncanonical raw term, intended to look like `1 + ω`.

Its exponents increase from `0` to `1`, so it is not in Cantor normal form.
-/
def badAscending : E0Term :=
  .cnf .zero 0 (.cnf E0Term.one 0 .zero)

example : E0Term.zero.isNormal = true := rfl
example : E0Term.one.isNormal = true := rfl
example : E0Term.badAscending.isNormal = false := rfl
example : E0Term.zero.IsNormal := rfl
example : E0Term.one.IsNormal := rfl
example : ¬ E0Term.badAscending.IsNormal := by decide

end E0Term

/--
Canonical ordinal notations below ε₀.

At this stage this is purely a syntactic subtype.  Later developments will give
it an order and prove that its semantic range is exactly the ordinals below
ε₀.
-/
abbrev E0 := { t : E0Term // t.IsNormal }

namespace E0

/-- The canonical notation for zero. -/
def zero : E0 :=
  ⟨.zero, rfl⟩

/-- The canonical notation for one. -/
def one : E0 :=
  ⟨E0Term.one, rfl⟩

end E0

end OrdinalAnalysis
