import OrdinalAnalysis.Gamma0.Term
import Mathlib.Tactic

/-!
# Raw comparison for Γ₀ terms

This file defines the executable comparison used by the Γ₀ notation system.

The comparison is purely syntactic. It does not interpret terms as mathlib
ordinals and it does not assume that the inputs are in Veblen normal form.

For leading Veblen principal terms, the recursion mirrors the shape of
mathlib's semantic theorem `Ordinal.cmp_veblen`:

- equal indices reduce to comparison of the arguments;
- a smaller left index reduces to comparing the left argument with the right
  principal term;
- a larger left index reduces to comparing the left principal term with the
  right argument.

Once the leading principal terms compare equal, stored coefficients and tails
are compared lexicographically.

Termination uses only the finite syntax: every recursive call strictly lowers
the sum of the two term node counts.
-/

namespace OrdinalAnalysis
namespace G0Term

/--
Executable comparison of raw Γ₀ terms.

For two nonzero terms, first compare their leading Veblen principal terms by
the recursive Veblen comparison rule. If the principal terms compare equal,
compare the stored positive coefficients and finally the tails.

The implementation is independent of abstract ordinal comparison. Later
semantic correctness will be proved only for canonical Veblen normal forms.
-/
def compareRaw (a b : G0Term) : Ordering :=
  match a, b with
  | .zero, .zero => .eq
  | .zero, .veblen _ _ _ _ => .lt
  | .veblen _ _ _ _, .zero => .gt
  | .veblen index arg coeff tail,
      .veblen index' arg' coeff' tail' =>
      let principalCmp :=
        match compareRaw index index' with
        | .eq => compareRaw arg arg'
        | .lt => compareRaw arg (principal index' arg')
        | .gt => compareRaw (principal index arg) arg'
      match principalCmp with
      | .lt => .lt
      | .gt => .gt
      | .eq =>
          match compare coeff coeff' with
          | .lt => .lt
          | .gt => .gt
          | .eq => compareRaw tail tail'
termination_by a.nodeCount + b.nodeCount
decreasing_by
  all_goals
    simp [nodeCount, principal]
    omega

/--
The proposition that one raw Γ₀ term is syntactically smaller than another.

We deliberately do not install this as the global `LT G0Term` instance:
the raw datatype contains noncanonical terms. The eventual canonical subtype
will receive the verified notation-system order.
-/
def RawLT (a b : G0Term) : Prop :=
  compareRaw a b = .lt

/-- Boolean form of raw syntactic strict comparison. -/
def rawLT (a b : G0Term) : Bool :=
  compareRaw a b == .lt

/-- Zero is raw-smaller than every nonzero raw Γ₀ term. -/
@[simp]
theorem rawLT_zero_veblen
    (index arg : G0Term) (coeff : Nat) (tail : G0Term) :
    RawLT .zero (.veblen index arg coeff tail) :=
  rfl

/-- No nonzero raw Γ₀ term is raw-smaller than zero. -/
@[simp]
theorem not_rawLT_veblen_zero
    (index arg : G0Term) (coeff : Nat) (tail : G0Term) :
    ¬ RawLT (.veblen index arg coeff tail) .zero := by
  simp [RawLT, compareRaw]

example : compareRaw G0Term.zero G0Term.zero = .eq := rfl
example : compareRaw G0Term.zero G0Term.one = .lt := rfl
example : compareRaw G0Term.one G0Term.zero = .gt := rfl
example : compareRaw G0Term.one G0Term.one = .eq := rfl
example : compareRaw G0Term.one G0Term.omega = .lt := rfl
example : compareRaw G0Term.omega G0Term.epsilonZero = .lt := rfl
example : RawLT G0Term.zero G0Term.one := rfl
example : rawLT G0Term.zero G0Term.one = true := rfl

end G0Term
end OrdinalAnalysis
