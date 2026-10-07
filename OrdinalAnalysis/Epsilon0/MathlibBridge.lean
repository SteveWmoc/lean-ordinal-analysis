import OrdinalAnalysis.Epsilon0.OrderEmbedding
import Mathlib.SetTheory.Ordinal.Notation

/-!
# Bridge to mathlib's ε₀ ordinal notations

Mathlib's `ONote` is a raw recursive syntax for ordinals below ε₀.  Its
constructor

```
ONote.oadd e n a
```

represents `ω ^ e * n + a`, with a positive coefficient `n : ℕ+`.

Our `E0Term.cnf e n a` stores the predecessor of that coefficient as a
plain natural number.  This file gives the structural conversion in both
directions and proves that the two raw syntaxes agree on both semantics and
comparison.

This bridge is deliberately at the raw-syntax level.  Normal-form
interoperability between `E0` and mathlib's `NONote` is a later layer.
-/

namespace OrdinalAnalysis
namespace E0Term

/-- Convert our raw ε₀ syntax to mathlib's `ONote`. -/
def toONote : E0Term → ONote
  | .zero => 0
  | .cnf exp coeff tail =>
      ONote.oadd exp.toONote coeff.succPNat tail.toONote

/-- Convert mathlib's raw `ONote` syntax to our `E0Term`. -/
def ofONote : ONote → E0Term
  | .zero => .zero
  | .oadd exp coeff tail =>
      .cnf exp.ofONote coeff.natPred tail.ofONote

@[simp]
theorem ofONote_toONote : ∀ t : E0Term, t.toONote.ofONote = t
  | .zero => rfl
  | .cnf exp coeff tail => by
      simp [toONote, ofONote, ofONote_toONote exp, ofONote_toONote tail]

@[simp]
theorem toONote_ofONote : ∀ o : ONote, o.ofONote.toONote = o
  | .zero => rfl
  | .oadd exp coeff tail => by
      simp [toONote, ofONote, toONote_ofONote exp, toONote_ofONote tail]

/-- The raw syntax conversion is an equivalence of finite datatypes. -/
def equivONote : E0Term ≃ ONote where
  toFun := toONote
  invFun := ofONote
  left_inv := ofONote_toONote
  right_inv := toONote_ofONote

/-- Our ordinal interpretation agrees with mathlib's `ONote.repr`. -/
@[simp]
theorem repr_toONote : ∀ t : E0Term, ONote.repr t.toONote = eval t
  | .zero => rfl
  | .cnf exp coeff tail => by
      simp [toONote, eval, repr_toONote exp, repr_toONote tail]

/-- The reverse raw conversion also preserves ordinal interpretation. -/
@[simp]
theorem eval_ofONote (o : ONote) :
    eval o.ofONote = ONote.repr o := by
  rw [← repr_toONote o.ofONote, toONote_ofONote]

/--
Mathlib's executable raw comparator agrees with ours under the syntax
conversion.
-/
@[simp]
theorem cmp_toONote : ∀ a b : E0Term,
    ONote.cmp a.toONote b.toONote = compareRaw a b := by
  intro a
  induction a with
  | zero =>
      intro b
      cases b <;> rfl
  | cnf exp coeff tail ihExp ihTail =>
      intro b
      cases b with
      | zero =>
          rfl
      | cnf exp' coeff' tail' =>
          simp only [toONote, ONote.cmp, ihExp exp', Nat.succPNat_coe]
          cases hExp : compareRaw exp exp' <;>
            simp [compareRaw, hExp, ihTail tail']

/-- The reverse conversion likewise preserves executable raw comparison. -/
@[simp]
theorem compareRaw_ofONote (a b : ONote) :
    compareRaw a.ofONote b.ofONote = ONote.cmp a b := by
  rw [← cmp_toONote a.ofONote b.ofONote, toONote_ofONote, toONote_ofONote]

end E0Term
end OrdinalAnalysis
