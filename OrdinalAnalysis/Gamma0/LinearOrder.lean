import OrdinalAnalysis.Gamma0.Uniqueness
import Mathlib.Order.Compare

/-!
# Linear order on canonical Γ₀ notations

The canonical subtype `G0` already carries the executable strict order induced
by `G0Term.compareRaw`.  Semantic correctness now lets us promote that relation
to a full linear order without replacing the underlying strict comparison.

The non-strict relation is defined through ordinal evaluation.  We first build
a preorder compatible with the existing raw strict order, then use
`linearOrderOfCompares` to certify the executable three-way comparator.

Canonical uniqueness supplies the equality case of comparison.
-/

namespace OrdinalAnalysis
namespace G0

/-- Non-strict order on canonical Γ₀ terms, transported through ordinal evaluation. -/
instance instLE : LE G0 where
  le a b := eval a ≤ eval b

/--
The semantic non-strict relation and the existing executable strict relation
form a preorder.
-/
instance instPreorder : Preorder G0 where
  le := fun a b => eval a ≤ eval b
  lt := fun a b => G0Term.RawLT a.1 b.1
  le_refl := fun _ => le_rfl
  le_trans := fun _ _ _ hab hbc => le_trans hab hbc
  lt_iff_le_not_ge := by
    intro a b
    rw [G0Term.rawLT_iff_eval_lt a.1 b.1 a.2 b.2]
    exact lt_iff_le_not_ge

/-- The raw comparator correctly reports the three possible relations on canonical terms. -/
theorem compareRaw_compares (a b : G0) :
    Ordering.Compares (G0Term.compareRaw a.1 b.1) a b := by
  cases hcmp : G0Term.compareRaw a.1 b.1 with
  | lt =>
      change a < b
      exact hcmp
  | eq =>
      change a = b
      apply Subtype.ext
      exact (G0Term.compareRaw_eq_eq_iff_of_normal a.1 b.1 a.2 b.2).1 hcmp
  | gt =>
      change b < a
      apply (lt_iff_eval_lt b a).2
      change G0Term.eval b.1 < G0Term.eval a.1
      apply (cmp_eq_gt_iff _ _).1
      rw [← G0Term.compareRaw_eq_cmp_eval_of_normal a.1 b.1 a.2 b.2]
      exact hcmp

/--
Canonical Γ₀ notations form a linear order whose strict comparison is the
executable raw comparator.
-/
instance instLinearOrder : LinearOrder G0 :=
  linearOrderOfCompares
    (fun a b : G0 => G0Term.compareRaw a.1 b.1)
    compareRaw_compares

/-- Canonical non-strict comparison agrees with ordinal comparison under evaluation. -/
theorem le_iff_eval_le (a b : G0) :
    a ≤ b ↔ eval a ≤ eval b :=
  Iff.rfl

end G0
end OrdinalAnalysis
