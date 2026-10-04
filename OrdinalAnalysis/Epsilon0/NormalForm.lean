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

/-- Zero is a canonical raw ε₀ term. -/
@[simp]
theorem isNormal_zero : E0Term.zero.IsNormal :=
  rfl

/--
Proposition-level characterization of normality for a CNF node.

This theorem is the proof-facing interface to the executable Boolean checker:
the exponent and tail must be normal, and a nonzero tail must begin with a
strictly smaller exponent.
-/
@[simp]
theorem isNormal_cnf_iff (exp : E0Term) (coeff : Nat) (tail : E0Term) :
    IsNormal (.cnf exp coeff tail) ↔
      IsNormal exp ∧
      IsNormal tail ∧
      match tail with
      | .zero => True
      | .cnf tailExp _ _ => RawLT tailExp exp := by
  cases tail with
  | zero =>
      simp [IsNormal, isNormal]
  | cnf tailExp tailCoeff tailTail =>
      simp [IsNormal, isNormal, RawLT, and_assoc]

/-- A CNF node with zero tail is normal exactly when its exponent is normal. -/
@[simp]
theorem isNormal_cnf_zero_iff (exp : E0Term) (coeff : Nat) :
    IsNormal (.cnf exp coeff .zero) ↔ IsNormal exp := by
  simp

/--
For a nonzero tail, normality exposes the three recursive conditions directly.
-/
@[simp]
theorem isNormal_cnf_cnf_iff
    (exp tailExp : E0Term) (coeff tailCoeff : Nat) (tailTail : E0Term) :
    IsNormal (.cnf exp coeff (.cnf tailExp tailCoeff tailTail)) ↔
      IsNormal exp ∧
      IsNormal (.cnf tailExp tailCoeff tailTail) ∧
      RawLT tailExp exp := by
  simp

/-- The exponent of a normal CNF node is normal. -/
theorem IsNormal.exp {exp : E0Term} {coeff : Nat} {tail : E0Term}
    (h : IsNormal (.cnf exp coeff tail)) :
    IsNormal exp :=
  (isNormal_cnf_iff exp coeff tail).1 h |>.1

/-- The tail of a normal CNF node is normal. -/
theorem IsNormal.tail {exp : E0Term} {coeff : Nat} {tail : E0Term}
    (h : IsNormal (.cnf exp coeff tail)) :
    IsNormal tail :=
  (isNormal_cnf_iff exp coeff tail).1 h |>.2.1

/-- The leading exponent of a nonzero normal tail is raw-smaller than the current exponent. -/
theorem IsNormal.tailExp_lt
    {exp tailExp : E0Term} {coeff tailCoeff : Nat} {tailTail : E0Term}
    (h : IsNormal (.cnf exp coeff (.cnf tailExp tailCoeff tailTail))) :
    RawLT tailExp exp :=
  (isNormal_cnf_cnf_iff exp tailExp coeff tailCoeff tailTail).1 h |>.2.2

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
