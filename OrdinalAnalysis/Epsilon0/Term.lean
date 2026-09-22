import OrdinalAnalysis.Basic
import Mathlib.Order.Std

/-!
# Raw ε₀ terms

This file defines the finite recursive syntax used for ordinal notations below
ε₀.  It intentionally does **not** impose Cantor normal form and does not
interpret terms as mathlib ordinals.

A nonzero term

```
E0Term.cnf exp coeff tail
```

is intended eventually to denote

```
ω ^ exp * (coeff + 1) + tail.
```

Thus the stored `coeff : Nat` is one less than the mathematical coefficient.
This keeps positivity out of the recursive datatype.
-/

namespace OrdinalAnalysis

/--
Raw finite syntax for Cantor-normal-form expressions below ε₀.

The datatype deliberately admits noncanonical terms.  Canonicality will be a
separate predicate in the next layer of the development.

Its `Ord` instance is the standard structural lexicographic comparison:
constructors are ordered as written, and fields of `cnf` are compared in the
order `exp`, `coeff`, `tail`.  The accompanying standard-library law
instances certify transitivity and agreement of comparison equality with
propositional equality, without installing `<` or `≤` on raw terms.
-/
inductive E0Term where
  | zero : E0Term
  | cnf (exp : E0Term) (coeff : Nat) (tail : E0Term) : E0Term
deriving DecidableEq, Repr, Ord, Std.TransOrd, Std.LawfulEqOrd

namespace E0Term

/-- The raw term intended to represent the ordinal `1`. -/
def one : E0Term :=
  .cnf .zero 0 .zero

/-- Test whether a raw term is syntactically zero. -/
def isZero : E0Term → Bool
  | .zero => true
  | .cnf _ _ _ => false

/-- The leading exponent of a nonzero raw term. -/
def leadingExponent? : E0Term → Option E0Term
  | .zero => none
  | .cnf exp _ _ => some exp

/--
The mathematical leading coefficient of a nonzero raw term.

If the constructor stores `coeff`, this returns `coeff + 1`.
-/
def leadingCoefficient? : E0Term → Option Nat
  | .zero => none
  | .cnf _ coeff _ => some coeff.succ

/-- The tail following the leading Cantor summand of a nonzero raw term. -/
def tail? : E0Term → Option E0Term
  | .zero => none
  | .cnf _ _ tail => some tail

/--
The number of constructor nodes in a raw term.

This is not an ordinal-theoretic rank.  It is a simple structural measure that
is useful for tests and may be useful for later termination arguments.
-/
def nodeCount : E0Term → Nat
  | .zero => 1
  | .cnf exp _ tail => 1 + exp.nodeCount + tail.nodeCount

example : E0Term.zero.isZero = true := rfl
example : E0Term.one.isZero = false := rfl
example : E0Term.one.leadingExponent? = some E0Term.zero := rfl
example : E0Term.one.leadingCoefficient? = some 1 := rfl
example : E0Term.one.tail? = some E0Term.zero := rfl
example : E0Term.one.nodeCount = 3 := rfl

end E0Term

end OrdinalAnalysis
