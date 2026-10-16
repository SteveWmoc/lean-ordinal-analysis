import OrdinalAnalysis.Basic

/-!
# Raw Γ₀ terms

This file begins the concrete Γ₀ notation system with finite recursive syntax.
It deliberately does **not** impose Veblen normal form and does not interpret
terms as mathlib ordinals.

A nonzero node

```
G0Term.veblen index arg coeff tail
```

is intended eventually to denote

```
φ_index(arg) * (coeff + 1) + tail,
```

where `φ` is the binary Veblen hierarchy implemented semantically by
`Ordinal.veblen`.

The stored `coeff : Nat` is one less than the mathematical coefficient, as in
`E0Term`. This keeps positivity out of the recursive datatype while allowing
repeated equal principal terms to be represented compactly.
-/

namespace OrdinalAnalysis

/--
Raw finite syntax for Veblen-normal-form expressions below Γ₀.

The datatype deliberately admits noncanonical terms. Canonicality and the
executable comparison algorithm are separate later layers.
-/
inductive G0Term where
  | zero : G0Term
  | veblen
      (index : G0Term)
      (arg : G0Term)
      (coeff : Nat)
      (tail : G0Term) : G0Term
deriving DecidableEq, Repr

namespace G0Term

/-- A single Veblen principal term `φ_index(arg)`. -/
def principal (index arg : G0Term) : G0Term :=
  .veblen index arg 0 .zero

/-- The raw term intended to represent the ordinal `1 = φ₀(0)`. -/
def one : G0Term :=
  principal .zero .zero

/-- The raw term intended to represent the ordinal `ω = φ₀(1)`. -/
def omega : G0Term :=
  principal .zero one

/-- The raw term intended to represent `ε₀ = φ₁(0)`. -/
def epsilonZero : G0Term :=
  principal one .zero

/-- Test whether a raw Γ₀ term is syntactically zero. -/
def isZero : G0Term → Bool
  | .zero => true
  | .veblen _ _ _ _ => false

/-- The Veblen index of the leading principal term. -/
def leadingIndex? : G0Term → Option G0Term
  | .zero => none
  | .veblen index _ _ _ => some index

/-- The Veblen argument of the leading principal term. -/
def leadingArgument? : G0Term → Option G0Term
  | .zero => none
  | .veblen _ arg _ _ => some arg

/--
The mathematical coefficient of the leading principal term.

If the constructor stores `coeff`, this returns `coeff + 1`.
-/
def leadingCoefficient? : G0Term → Option Nat
  | .zero => none
  | .veblen _ _ coeff _ => some coeff.succ

/-- The tail following the leading Veblen summand. -/
def tail? : G0Term → Option G0Term
  | .zero => none
  | .veblen _ _ _ tail => some tail

/--
The number of constructor nodes in a raw Γ₀ term.

This is a structural measure, not an ordinal-theoretic rank. It is intended to
support tests and later termination arguments for recursive comparison.
-/
def nodeCount : G0Term → Nat
  | .zero => 1
  | .veblen index arg _ tail =>
      1 + index.nodeCount + arg.nodeCount + tail.nodeCount

example : G0Term.zero.isZero = true := rfl
example : G0Term.one.isZero = false := rfl
example : G0Term.one.leadingIndex? = some G0Term.zero := rfl
example : G0Term.one.leadingArgument? = some G0Term.zero := rfl
example : G0Term.one.leadingCoefficient? = some 1 := rfl
example : G0Term.one.tail? = some G0Term.zero := rfl
example : G0Term.one.nodeCount = 4 := rfl

example : G0Term.omega.leadingIndex? = some G0Term.zero := rfl
example : G0Term.omega.leadingArgument? = some G0Term.one := rfl

example : G0Term.epsilonZero.leadingIndex? = some G0Term.one := rfl
example : G0Term.epsilonZero.leadingArgument? = some G0Term.zero := rfl

end G0Term
end OrdinalAnalysis
