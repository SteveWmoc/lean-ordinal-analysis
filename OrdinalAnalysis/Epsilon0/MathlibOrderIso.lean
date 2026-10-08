import OrdinalAnalysis.Epsilon0.CanonicalBridge

/-!
# Order isomorphism with mathlib's canonical ε₀ notations

The canonical bridge already identifies `E0` with mathlib's `NONote` as
types and shows that both interpretations have the same ordinal value.

This file records the corresponding order-level interface.  The resulting
order isomorphism lets later developments transport arithmetic and fundamental
sequence constructions from mathlib without changing this project's
syntax-first definition of comparison.
-/

namespace OrdinalAnalysis
namespace E0

/-- The executable three-way comparator on canonical ε₀ notations. -/
def cmp (a b : E0) : Ordering :=
  E0Term.compareRaw a.1 b.1

/-- The canonical comparator agrees exactly with mathlib's `NONote.cmp`. -/
@[simp]
theorem cmp_toNONote (a b : E0) :
    NONote.cmp (toNONote a) (toNONote b) = cmp a b := by
  simp [NONote.cmp, toNONote, cmp]

/-- The bridge reflects and preserves strict order. -/
@[simp]
theorem toNONote_lt_toNONote_iff (a b : E0) :
    toNONote a < toNONote b ↔ a < b := by
  change NONote.repr (toNONote a) < NONote.repr (toNONote b) ↔ a < b
  rw [repr_toNONote, repr_toNONote]
  exact (lt_iff_eval_lt a b).symm

/-- The bridge reflects and preserves non-strict order. -/
@[simp]
theorem toNONote_le_toNONote_iff (a b : E0) :
    toNONote a ≤ toNONote b ↔ a ≤ b := by
  change NONote.repr (toNONote a) ≤ NONote.repr (toNONote b) ↔ a ≤ b
  rw [repr_toNONote, repr_toNONote]
  exact (le_iff_eval_le a b).symm

/--
Canonical ε₀ notations in this project and mathlib's `NONote` are order
isomorphic.
-/
noncomputable def orderIsoNONote : E0 ≃o NONote :=
  { equivNONote with
    map_rel_iff' := fun {a b} => toNONote_le_toNONote_iff a b }

/-- The order isomorphism uses the existing canonical conversion. -/
@[simp]
theorem orderIsoNONote_apply (a : E0) :
    orderIsoNONote a = toNONote a :=
  rfl

/-- The inverse order isomorphism uses the existing reverse conversion. -/
@[simp]
theorem orderIsoNONote_symm_apply (o : NONote) :
    orderIsoNONote.symm o = ofNONote o :=
  rfl

end E0
end OrdinalAnalysis
