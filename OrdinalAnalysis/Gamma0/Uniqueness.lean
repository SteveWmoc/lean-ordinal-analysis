import OrdinalAnalysis.Gamma0.Correctness

/-!
# Uniqueness of canonical Γ₀ notations

Raw Veblen syntax is intentionally redundant. For example, malformed terms can
represent the same Veblen principal value through a fixed-point collapse.

Canonical normality removes exactly those aliases. This file proves that an
`Ordering.eq` result from the executable comparator forces literal equality
of normal raw terms, and hence that ordinal evaluation is injective on `G0`.
-/

namespace OrdinalAnalysis
namespace G0Term

open Ordinal

/--
A principal term is normal when its index and argument are normal and the
argument satisfies the canonical Veblen side condition.
-/
theorem IsNormal.principal
    {index arg : G0Term}
    (hindex : IsNormal index)
    (harg : IsNormal arg)
    (hside : RawLT arg (principal index arg)) :
    IsNormal (principal index arg) := by
  simpa [principal] using
    (isNormal_veblen_zero_iff index arg 0).2 ⟨hindex, harg, hside⟩

/--
On normal Γ₀ terms, the executable raw comparator returns `.eq` exactly for
literal syntactic equality.

This is false for arbitrary raw terms: the canonical Veblen side condition is
what rules out fixed-point aliases.
-/
theorem compareRaw_eq_eq_iff_of_normal :
    ∀ a b : G0Term,
      IsNormal a →
      IsNormal b →
      (compareRaw a b = .eq ↔ a = b) := by
  intro a
  induction a with
  | zero =>
      intro b ha hb
      cases b <;> simp [compareRaw]
  | veblen index arg coeff tail ihIndex ihArg ihTail =>
      intro b ha hb
      cases b with
      | zero =>
          simp [compareRaw]
      | veblen index' arg' coeff' tail' =>
          constructor
          · intro hEq
            have haIndex := ha.index
            have haArg := ha.arg
            have haTail := ha.tail
            have hbIndex := hb.index
            have hbArg := hb.arg
            have hbTail := hb.tail
            have haPrincipal :
                IsNormal (principal index arg) :=
              IsNormal.principal haIndex haArg ha.arg_lt_principal
            have hbPrincipal :
                IsNormal (principal index' arg') :=
              IsNormal.principal hbIndex hbArg hb.arg_lt_principal
            cases hIndex : compareRaw index index' with
            | eq =>
                have hIndexEq : index = index' :=
                  (ihIndex index' haIndex hbIndex).1 hIndex
                subst index'
                cases hArg : compareRaw arg arg' with
                | lt =>
                    simp [compareRaw, hIndex, hArg] at hEq
                | gt =>
                    simp [compareRaw, hIndex, hArg] at hEq
                | eq =>
                    have hArgEq : arg = arg' :=
                      (ihArg arg' haArg hbArg).1 hArg
                    subst arg'
                    cases hCoeff : compare coeff coeff' with
                    | lt =>
                        simp [compareRaw, hIndex, hArg, hCoeff] at hEq
                    | gt =>
                        simp [compareRaw, hIndex, hArg, hCoeff] at hEq
                    | eq =>
                        have hCoeffEq : coeff = coeff' :=
                          Nat.compare_eq_eq.mp hCoeff
                        subst coeff'
                        cases hTail : compareRaw tail tail' with
                        | lt =>
                            simp [compareRaw, hIndex, hArg, hCoeff, hTail] at hEq
                        | gt =>
                            simp [compareRaw, hIndex, hArg, hCoeff, hTail] at hEq
                        | eq =>
                            have hTailEq : tail = tail' :=
                              (ihTail tail' haTail hbTail).1 hTail
                            subst tail'
                            rfl
            | lt =>
                cases hPrincipal :
                    compareRaw arg (principal index' arg') with
                | lt =>
                    simp [compareRaw, hIndex, hPrincipal] at hEq
                | gt =>
                    simp [compareRaw, hIndex, hPrincipal] at hEq
                | eq =>
                    have hIndexSem : eval index < eval index' :=
                      (rawLT_iff_eval_lt index index' haIndex hbIndex).1 hIndex
                    have hArgPrincipalEq :
                        eval arg = eval (principal index' arg') := by
                      have hcmp :=
                        compareRaw_eq_cmp_eval_of_normal
                          arg (principal index' arg') haArg hbPrincipal
                      apply (cmp_eq_eq_iff _ _).1
                      rw [← hcmp]
                      exact hPrincipal
                    have hVeblenEq :
                        Ordinal.veblen (eval index) (eval arg) =
                          Ordinal.veblen (eval index') (eval arg') := by
                      apply Ordinal.veblen_eq_veblen_iff.2
                      exact Or.inr <| Or.inl ⟨hIndexSem, by
                        simpa [eval_principal] using hArgPrincipalEq⟩
                    have hArgLt :
                        eval arg < eval (principal index arg) :=
                      (rawLT_iff_eval_lt
                        arg (principal index arg) haArg haPrincipal).1
                        ha.arg_lt_principal
                    have hbad : eval arg < eval arg := by
                      calc
                        eval arg < eval (principal index arg) := hArgLt
                        _ = eval (principal index' arg') := by
                          simpa [eval_principal] using hVeblenEq
                        _ = eval arg := hArgPrincipalEq.symm
                    exact (lt_irrefl _ hbad).elim
            | gt =>
                cases hPrincipal :
                    compareRaw (principal index arg) arg' with
                | lt =>
                    simp [compareRaw, hIndex, hPrincipal] at hEq
                | gt =>
                    simp [compareRaw, hIndex, hPrincipal] at hEq
                | eq =>
                    have hIndexSem : eval index' < eval index :=
                      (rawLT_iff_eval_lt index' index hbIndex haIndex).1 <| by
                        have hcmp :=
                          compareRaw_eq_cmp_eval_of_normal
                            index index' haIndex hbIndex
                        have hsem : cmp (eval index) (eval index') = .gt := by
                          rw [← hcmp]
                          exact hIndex
                        exact (cmp_eq_gt_iff _ _).1 hsem
                    have hPrincipalArgEq :
                        eval (principal index arg) = eval arg' := by
                      have hcmp :=
                        compareRaw_eq_cmp_eval_of_normal
                          (principal index arg) arg' haPrincipal hbArg
                      apply (cmp_eq_eq_iff _ _).1
                      rw [← hcmp]
                      exact hPrincipal
                    have hVeblenEq :
                        Ordinal.veblen (eval index) (eval arg) =
                          Ordinal.veblen (eval index') (eval arg') := by
                      apply Ordinal.veblen_eq_veblen_iff.2
                      exact Or.inr <| Or.inr ⟨hIndexSem, by
                        simpa [eval_principal] using hPrincipalArgEq⟩
                    have hArgLt :
                        eval arg' < eval (principal index' arg') :=
                      (rawLT_iff_eval_lt
                        arg' (principal index' arg') hbArg hbPrincipal).1
                        hb.arg_lt_principal
                    have hbad : eval arg' < eval arg' := by
                      calc
                        eval arg' < eval (principal index' arg') := hArgLt
                        _ = eval (principal index arg) := by
                          simpa [eval_principal] using hVeblenEq.symm
                        _ = eval arg' := hPrincipalArgEq
                    exact (lt_irrefl _ hbad).elim
          · intro hab
            subst b
            have hcmp :=
              compareRaw_eq_cmp_eval_of_normal
                (.veblen index arg coeff tail)
                (.veblen index arg coeff tail) ha ha
            rw [hcmp]
            exact (cmp_eq_eq_iff _ _).2 rfl

end G0Term

namespace G0

/-- Canonical Γ₀ evaluation is injective. -/
theorem eval_injective : Function.Injective eval := by
  intro a b hab
  apply Subtype.ext
  apply
    (G0Term.compareRaw_eq_eq_iff_of_normal
      a.1 b.1 a.2 b.2).1
  have hcmp :=
    G0Term.compareRaw_eq_cmp_eval_of_normal
      a.1 b.1 a.2 b.2
  rw [hcmp]
  exact (cmp_eq_eq_iff _ _).2 hab

/-- Semantic equality reflects exactly literal equality of canonical notations. -/
@[simp]
theorem eval_eq_eval_iff (a b : G0) :
    eval a = eval b ↔ a = b :=
  eval_injective.eq_iff

end G0
end OrdinalAnalysis
