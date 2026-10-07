import OrdinalAnalysis.Epsilon0.MathlibBridge

/-!
# Canonical bridge to mathlib's ε₀ notations

The raw bridge identifies `E0Term` with mathlib's `ONote`.  This file shows
that the identification also preserves the normal-form invariant.

The key mathlib theorem is `ONote.nfBelow_iff_topBelow`: for a normal
exponent, a tail is bounded below its leading power exactly when the tail is
normal and its top exponent compares strictly smaller.  This is precisely the
condition checked by `E0Term.IsNormal`.

We then lift the raw equivalence to canonical notations `E0` and `NONote`.
-/

namespace OrdinalAnalysis
namespace E0Term

/-- Our normal-form predicate agrees with mathlib's `ONote.NF`. -/
theorem isNormal_iff_nf_toONote : ∀ t : E0Term,
    IsNormal t ↔ ONote.NF t.toONote := by
  intro t
  induction t with
  | zero =>
      constructor
      · intro _
        exact ONote.NF.zero
      · intro _
        exact isNormal_zero
  | cnf exp coeff tail ihExp ihTail =>
      cases tail with
      | zero =>
          constructor
          · intro h
            have hnfExp : ONote.NF exp.toONote :=
              ihExp.mp h.exp
            exact @ONote.NF.oadd_zero exp.toONote coeff.succPNat hnfExp
          · intro h
            exact
              (isNormal_cnf_zero_iff exp coeff).2
                (ihExp.mpr h.fst)
      | cnf tailExp tailCoeff tailTail =>
          constructor
          · intro h
            have hnfExp : ONote.NF exp.toONote :=
              ihExp.mp h.exp
            have hnfTail :
                ONote.NF (toONote (.cnf tailExp tailCoeff tailTail)) :=
              ihTail.mp h.tail
            have htop :
                ONote.TopBelow exp.toONote
                  (toONote (.cnf tailExp tailCoeff tailTail)) := by
              simpa [ONote.TopBelow, toONote, RawLT] using h.tailExp_lt
            have hbelow :
                ONote.NFBelow
                  (toONote (.cnf tailExp tailCoeff tailTail))
                  (ONote.repr exp.toONote) :=
              (@ONote.nfBelow_iff_topBelow exp.toONote hnfExp
                (toONote (.cnf tailExp tailCoeff tailTail))).2
                ⟨hnfTail, htop⟩
            exact ONote.NF.oadd hnfExp coeff.succPNat hbelow
          · intro h
            have hnfExp : ONote.NF exp.toONote :=
              h.fst
            have hnfTail :
                ONote.NF (toONote (.cnf tailExp tailCoeff tailTail)) :=
              h.snd
            have htop :
                ONote.TopBelow exp.toONote
                  (toONote (.cnf tailExp tailCoeff tailTail)) :=
              ((@ONote.nfBelow_iff_topBelow exp.toONote hnfExp
                (toONote (.cnf tailExp tailCoeff tailTail))).1 h.snd').2
            have htailLt : RawLT tailExp exp := by
              simpa [ONote.TopBelow, toONote, RawLT] using htop
            exact
              (isNormal_cnf_cnf_iff
                exp tailExp coeff tailCoeff tailTail).2
                ⟨ihExp.mpr hnfExp, ihTail.mpr hnfTail, htailLt⟩

/-- Mathlib normality is preserved by conversion back to our raw syntax. -/
theorem isNormal_ofONote_iff (o : ONote) :
    IsNormal (ofONote o) ↔ ONote.NF o := by
  rw [isNormal_iff_nf_toONote, toONote_ofONote]

end E0Term

namespace E0

/-- Convert a canonical `E0` term to mathlib's canonical `NONote`. -/
def toNONote (a : E0) : NONote :=
  ⟨a.1.toONote, (E0Term.isNormal_iff_nf_toONote a.1).1 a.2⟩

/-- Convert a mathlib `NONote` to our canonical `E0` type. -/
def ofNONote (o : NONote) : E0 :=
  ⟨E0Term.ofONote o.1, (E0Term.isNormal_ofONote_iff o.1).2 o.2⟩

@[simp]
theorem ofNONote_toNONote (a : E0) :
    ofNONote (toNONote a) = a := by
  apply Subtype.ext
  simp [ofNONote, toNONote]

@[simp]
theorem toNONote_ofNONote (o : NONote) :
    toNONote (ofNONote o) = o := by
  apply Subtype.ext
  simp [ofNONote, toNONote]

/-- Canonical ε₀ notations are equivalent to mathlib's `NONote`. -/
def equivNONote : E0 ≃ NONote where
  toFun := toNONote
  invFun := ofNONote
  left_inv := ofNONote_toNONote
  right_inv := toNONote_ofNONote

/-- The canonical bridge commutes with ordinal interpretation. -/
@[simp]
theorem repr_toNONote (a : E0) :
    NONote.repr (toNONote a) = eval a := by
  simp [NONote.repr, toNONote, eval]

/-- The reverse canonical bridge also preserves ordinal interpretation. -/
@[simp]
theorem eval_ofNONote (o : NONote) :
    eval (ofNONote o) = NONote.repr o := by
  rw [← repr_toNONote (ofNONote o), toNONote_ofNONote]

end E0
end OrdinalAnalysis
