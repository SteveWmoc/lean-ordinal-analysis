import OrdinalAnalysis.Epsilon0.Correctness
import Mathlib.Order.Compare

/-!
# Linear order on canonical ε₀ notations

The canonical subtype `E0` already carries the executable strict order induced
by `E0Term.compareRaw`.  Semantic correctness now lets us promote that relation
to a full linear order without replacing the underlying strict comparison.

The non-strict relation is defined through ordinal evaluation.  We first build
a preorder compatible with the existing raw strict order, then use
`linearOrderOfCompares` to certify the executable three-way comparator.

As a first payoff, ordinal evaluation is injective on canonical ε₀ terms.
-/

namespace OrdinalAnalysis
namespace E0

/-- Non-strict order on canonical ε₀ terms, transported through ordinal evaluation. -/
noncomputable instance instLE : LE E0 where
  le a b := eval a ≤ eval b

/--
The semantic non-strict relation and the existing executable strict relation
form a preorder.
-/
noncomputable instance instPreorder : Preorder E0 where
  le := fun a b => eval a ≤ eval b
  lt := fun a b => E0Term.RawLT a.1 b.1
  le_refl := fun _ => le_rfl
  le_trans := fun _ _ _ hab hbc => le_trans hab hbc
  lt_iff_le_not_ge := by
    intro a b
    rw [E0Term.rawLT_iff_eval_lt a.1 b.1 a.2 b.2]
    exact lt_iff_le_not_ge

/-- The raw comparator correctly reports the three possible relations on canonical terms. -/
theorem compareRaw_compares (a b : E0) :
    Ordering.Compares (E0Term.compareRaw a.1 b.1) a b := by
  cases hcmp : E0Term.compareRaw a.1 b.1 with
  | lt =>
      change a < b
      exact hcmp
  | eq =>
      change a = b
      apply Subtype.ext
      exact (E0Term.compareRaw_eq_eq_iff a.1 b.1).1 hcmp
  | gt =>
      change b < a
      exact (E0Term.compareRaw_eq_gt_iff_reverse_rawLT a.1 b.1).1 hcmp

/--
Canonical ε₀ notations form a linear order whose strict comparison is the
executable raw comparator.
-/
noncomputable instance instLinearOrder : LinearOrder E0 :=
  linearOrderOfCompares
    (fun a b : E0 => E0Term.compareRaw a.1 b.1)
    compareRaw_compares

/-- Canonical non-strict comparison agrees with ordinal comparison under evaluation. -/
theorem le_iff_eval_le (a b : E0) :
    a ≤ b ↔ eval a ≤ eval b :=
  Iff.rfl

/-- Ordinal evaluation is injective on canonical ε₀ notations. -/
theorem eval_injective : Function.Injective eval := by
  intro a b h
  apply le_antisymm
  · exact (le_iff_eval_le a b).2 h.le
  · exact (le_iff_eval_le b a).2 h.ge

end E0
end OrdinalAnalysis
