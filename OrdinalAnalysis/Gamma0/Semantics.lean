import OrdinalAnalysis.Gamma0.Order

/-!
# Semantics of Γ₀ notation terms

This file interprets raw Γ₀ syntax in mathlib's abstract `Ordinal` type.

The interpretation is deliberately separate from the executable syntax,
normal-form checker, and raw comparison algorithm. It is a specification used
to certify those computational layers rather than an implementation of them.
-/

namespace OrdinalAnalysis
namespace G0Term

open Ordinal

/--
Interpret a raw Γ₀ term as a mathlib ordinal.

The semantic codomain is fixed at `Ordinal.{0}`. A nonzero constructor

```
veblen index arg coeff tail
```

is interpreted as

```
Ordinal.veblen (eval index) (eval arg) * (coeff + 1) + eval tail.
```

The stored natural coefficient is one less than the represented positive
coefficient.
-/
noncomputable def eval : G0Term → Ordinal.{0}
  | .zero => 0
  | .veblen index arg coeff tail =>
      Ordinal.veblen (eval index) (eval arg) *
          (coeff.succ : Ordinal.{0}) +
        eval tail

@[simp]
theorem eval_zero : eval .zero = 0 :=
  rfl

@[simp]
theorem eval_veblen
    (index arg : G0Term) (coeff : Nat) (tail : G0Term) :
    eval (.veblen index arg coeff tail) =
      Ordinal.veblen (eval index) (eval arg) *
          (coeff.succ : Ordinal.{0}) +
        eval tail :=
  rfl

/-- A single raw principal term evaluates to the corresponding Veblen value. -/
@[simp]
theorem eval_principal (index arg : G0Term) :
    eval (principal index arg) =
      Ordinal.veblen (eval index) (eval arg) := by
  simp [principal]

@[simp]
theorem eval_one : eval G0Term.one = 1 := by
  simp [G0Term.one, Ordinal.veblen_zero_apply]

@[simp]
theorem eval_omega : eval G0Term.omega = Ordinal.omega0 := by
  simp [G0Term.omega, Ordinal.veblen_zero_apply]

@[simp]
theorem eval_epsilonZero : eval G0Term.epsilonZero = ε₀ := by
  simp [G0Term.epsilonZero]

end G0Term

namespace G0

open Ordinal

/--
Interpret a canonical Γ₀ notation as an ordinal.

Canonicality is not needed to define the map; it becomes essential when
proving comparison correctness, injectivity, the Γ₀ upper bound, and exact
completeness below Γ₀.
-/
noncomputable def eval (a : G0) : Ordinal.{0} :=
  G0Term.eval a.1

@[simp]
theorem eval_zero : eval G0.zero = 0 := by
  simp [eval, G0.zero]

@[simp]
theorem eval_one : eval G0.one = 1 := by
  simp [eval, G0.one]

@[simp]
theorem eval_omega : eval G0.omega = Ordinal.omega0 := by
  simp [eval, G0.omega]

@[simp]
theorem eval_epsilonZero : eval G0.epsilonZero = ε₀ := by
  simp [eval, G0.epsilonZero]

end G0
end OrdinalAnalysis
