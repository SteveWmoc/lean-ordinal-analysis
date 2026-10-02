import OrdinalAnalysis.Epsilon0.Order
import Mathlib.SetTheory.Ordinal.Exponential

/-!
# Semantics of ε₀ notation terms

This file gives raw ε₀ syntax its intended interpretation in mathlib's
abstract type `Ordinal`.

The interpretation is deliberately separate from the executable syntax and
comparison algorithms.  It will be used to certify those algorithms rather
than to implement them.
-/

namespace OrdinalAnalysis
namespace E0Term

/--
Interpret a raw ε₀ term as a mathlib ordinal.

The semantic codomain is fixed at `Ordinal.{0}`. Since `E0Term` is a
first-order finite syntax living in `Type`, no universe polymorphism is
needed here, and fixing the codomain prevents independent occurrences of
`eval` from elaborating at incompatible ordinal universes.

The constructor

```
cnf exp coeff tail
```

is interpreted as

```
ω ^ eval exp * (coeff + 1) + eval tail.
```

Recall that the stored natural coefficient is one less than the represented
positive coefficient.
-/
noncomputable def eval : E0Term → Ordinal.{0}
  | .zero => 0
  | .cnf exp coeff tail =>
      (Ordinal.omega0 : Ordinal.{0}) ^ eval exp *
          (coeff.succ : Ordinal.{0}) +
        eval tail

@[simp]
theorem eval_zero : eval .zero = 0 :=
  rfl

@[simp]
theorem eval_cnf (exp : E0Term) (coeff : Nat) (tail : E0Term) :
    eval (.cnf exp coeff tail) =
      (Ordinal.omega0 : Ordinal.{0}) ^ eval exp *
          (coeff.succ : Ordinal.{0}) +
        eval tail :=
  rfl

@[simp]
theorem eval_one : eval E0Term.one = 1 := by
  simp [E0Term.one, eval]

end E0Term

namespace E0

/--
Interpret a canonical ε₀ notation as an ordinal.

Canonicality is not needed to define the map; it becomes essential when we
prove injectivity, comparison correctness, and the exact range below ε₀.
-/
noncomputable def eval (a : E0) : Ordinal.{0} :=
  E0Term.eval a.1

@[simp]
theorem eval_zero : eval E0.zero = 0 := by
  simp [eval, E0.zero]

@[simp]
theorem eval_one : eval E0.one = 1 := by
  simp [eval, E0.one]

end E0
end OrdinalAnalysis
