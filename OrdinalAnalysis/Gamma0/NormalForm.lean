import OrdinalAnalysis.Gamma0.Compare

/-!
# Veblen normal form below Γ₀

This file separates canonical Γ₀ notations from the raw recursive syntax.

A nonzero term

```
G0Term.veblen index arg coeff tail
```

is canonical when:

* the Veblen index is canonical;
* the Veblen argument is canonical;
* the tail is canonical;
* the argument satisfies the canonical Veblen side condition
  `arg < φ_index(arg)`; and
* if the tail is nonzero, its leading Veblen principal term is strictly
  smaller than the current leading principal term.

All comparisons in the checker are performed by the executable raw comparator.
No semantic `Ordinal` evaluation is used.
-/

namespace OrdinalAnalysis
namespace G0Term

/--
Executable Veblen-normal-form check for raw Γ₀ terms.

The side condition `arg < principal index arg` rules out noncanonical
presentations in which the argument is already a fixed point of the selected
Veblen function. The tail condition enforces a strictly descending finite sum
of Veblen principal terms.
-/
def isNormal : G0Term → Bool
  | .zero => true
  | .veblen index arg _ tail =>
      isNormal index &&
      isNormal arg &&
      isNormal tail &&
      rawLT arg (principal index arg) &&
      match tail with
      | .zero => true
      | .veblen tailIndex tailArg _ _ =>
          rawLT (principal tailIndex tailArg) (principal index arg)

/-- A raw Γ₀ term is canonical exactly when the executable normal-form check succeeds. -/
def IsNormal (t : G0Term) : Prop :=
  t.isNormal = true

instance instDecidableIsNormal (t : G0Term) : Decidable t.IsNormal := by
  unfold IsNormal
  exact decEq t.isNormal true

/-- Zero is a canonical raw Γ₀ term. -/
@[simp]
theorem isNormal_zero : G0Term.zero.IsNormal :=
  rfl

/--
Proposition-level characterization of Veblen normality for a nonzero node.
-/
@[simp]
theorem isNormal_veblen_iff
    (index arg : G0Term) (coeff : Nat) (tail : G0Term) :
    IsNormal (.veblen index arg coeff tail) ↔
      IsNormal index ∧
      IsNormal arg ∧
      IsNormal tail ∧
      RawLT arg (principal index arg) ∧
      match tail with
      | .zero => True
      | .veblen tailIndex tailArg _ _ =>
          RawLT
            (principal tailIndex tailArg)
            (principal index arg) := by
  cases tail with
  | zero =>
      simp [IsNormal, isNormal, rawLT, RawLT, and_assoc]
  | veblen tailIndex tailArg tailCoeff tailTail =>
      simp [IsNormal, isNormal, rawLT, RawLT, and_assoc]

/--
A Veblen node with zero tail is normal exactly when its index and argument are
normal and its argument satisfies the canonical Veblen side condition.
-/
@[simp]
theorem isNormal_veblen_zero_iff
    (index arg : G0Term) (coeff : Nat) :
    IsNormal (.veblen index arg coeff .zero) ↔
      IsNormal index ∧
      IsNormal arg ∧
      RawLT arg (principal index arg) := by
  simp

/--
For a nonzero tail, normality exposes all five recursive/canonical conditions.
-/
@[simp]
theorem isNormal_veblen_veblen_iff
    (index arg tailIndex tailArg : G0Term)
    (coeff tailCoeff : Nat) (tailTail : G0Term) :
    IsNormal
      (.veblen index arg coeff
        (.veblen tailIndex tailArg tailCoeff tailTail)) ↔
      IsNormal index ∧
      IsNormal arg ∧
      IsNormal (.veblen tailIndex tailArg tailCoeff tailTail) ∧
      RawLT arg (principal index arg) ∧
      RawLT
        (principal tailIndex tailArg)
        (principal index arg) := by
  simp

/-- The Veblen index of a normal nonzero node is normal. -/
theorem IsNormal.index
    {index arg : G0Term} {coeff : Nat} {tail : G0Term}
    (h : IsNormal (.veblen index arg coeff tail)) :
    IsNormal index :=
  (isNormal_veblen_iff index arg coeff tail).1 h |>.1

/-- The Veblen argument of a normal nonzero node is normal. -/
theorem IsNormal.arg
    {index arg : G0Term} {coeff : Nat} {tail : G0Term}
    (h : IsNormal (.veblen index arg coeff tail)) :
    IsNormal arg :=
  (isNormal_veblen_iff index arg coeff tail).1 h |>.2.1

/-- The tail of a normal nonzero node is normal. -/
theorem IsNormal.tail
    {index arg : G0Term} {coeff : Nat} {tail : G0Term}
    (h : IsNormal (.veblen index arg coeff tail)) :
    IsNormal tail :=
  (isNormal_veblen_iff index arg coeff tail).1 h |>.2.2.1

/-- The argument of a normal Veblen principal term is raw-smaller than that principal term. -/
theorem IsNormal.arg_lt_principal
    {index arg : G0Term} {coeff : Nat} {tail : G0Term}
    (h : IsNormal (.veblen index arg coeff tail)) :
    RawLT arg (principal index arg) :=
  (isNormal_veblen_iff index arg coeff tail).1 h |>.2.2.2.1

/-- A nonzero normal tail begins with a strictly smaller Veblen principal term. -/
theorem IsNormal.tailPrincipal_lt
    {index arg tailIndex tailArg : G0Term}
    {coeff tailCoeff : Nat} {tailTail : G0Term}
    (h :
      IsNormal
        (.veblen index arg coeff
          (.veblen tailIndex tailArg tailCoeff tailTail))) :
    RawLT
      (principal tailIndex tailArg)
      (principal index arg) :=
  (isNormal_veblen_veblen_iff
      index arg tailIndex tailArg coeff tailCoeff tailTail).1 h |>.2.2.2.2

/--
A deliberately noncanonical raw term whose argument is already fixed by the
selected Veblen function.

Syntactically this is `φ₀(ε₀)`; its argument compares equal to the whole
principal term, so the required strict side condition fails.
-/
def badFixedPoint : G0Term :=
  principal .zero epsilonZero

/--
A deliberately noncanonical ascending sum, intended to look like
`φ₀(0) + φ₀(1)`.
-/
def badAscending : G0Term :=
  .veblen .zero .zero 0 omega

example : G0Term.zero.isNormal = true := by native_decide
example : G0Term.one.isNormal = true := by native_decide
example : G0Term.omega.isNormal = true := by native_decide
example : G0Term.epsilonZero.isNormal = true := by native_decide
example : G0Term.badFixedPoint.isNormal = false := by native_decide
example : G0Term.badAscending.isNormal = false := by native_decide

example : G0Term.zero.IsNormal := by native_decide
example : G0Term.one.IsNormal := by native_decide
example : G0Term.omega.IsNormal := by native_decide
example : G0Term.epsilonZero.IsNormal := by native_decide
example : ¬ G0Term.badFixedPoint.IsNormal := by native_decide
example : ¬ G0Term.badAscending.IsNormal := by native_decide

end G0Term

/--
Canonical Veblen-normal-form notations intended to represent exactly the
ordinals below Γ₀.

At this stage this is still a syntactic subtype. Later layers will give it a
verified order and semantic interpretation.
-/
abbrev G0 := { t : G0Term // t.IsNormal }

namespace G0

/-- The canonical Γ₀ notation for zero. -/
def zero : G0 :=
  ⟨.zero, by native_decide⟩

/-- The canonical Γ₀ notation for one. -/
def one : G0 :=
  ⟨G0Term.one, by native_decide⟩

/-- The canonical Γ₀ notation for ω. -/
def omega : G0 :=
  ⟨G0Term.omega, by native_decide⟩

/-- The canonical Γ₀ notation for ε₀. -/
def epsilonZero : G0 :=
  ⟨G0Term.epsilonZero, by native_decide⟩

end G0
end OrdinalAnalysis
