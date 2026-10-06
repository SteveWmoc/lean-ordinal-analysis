import OrdinalAnalysis.Epsilon0.SemanticCompare

/-!
# Soundness of ε₀ raw comparison on normal terms

This file begins the recursive correctness proof for the ε₀ notation system.

Two facts are proved mutually:

* the tail of a normal CNF node evaluates below its leading power of `ω`;
* strict raw syntactic comparison of normal terms implies strict comparison of
  their ordinal interpretations.

The mutual recursion reflects the mathematics directly.  The tail bound needs
comparison soundness for the tail's leading exponent, while comparison
soundness needs the source tail bound in the exponent and coefficient cases.
-/

namespace OrdinalAnalysis
namespace E0Term

mutual

/--
The tail of a normal CNF node lies strictly below its leading power of `ω`.
-/
theorem eval_tail_lt_leadingPower_of_normal
    (exp : E0Term) (coeff : Nat) (tail : E0Term)
    (h : IsNormal (.cnf exp coeff tail)) :
    eval tail < (Ordinal.omega0 : Ordinal.{0}) ^ eval exp := by
  cases tail with
  | zero =>
      simpa using
        (Ordinal.opow_pos (eval exp) (Ordinal.omega0_pos : 0 < (Ordinal.omega0 : Ordinal.{0})))
  | cnf tailExp tailCoeff tailTail =>
      have htailNormal :
          IsNormal (.cnf tailExp tailCoeff tailTail) :=
        h.tail
      have htailExpNormal : IsNormal tailExp :=
        htailNormal.exp
      have hexpNormal : IsNormal exp :=
        h.exp
      have htailExpRawLT : RawLT tailExp exp :=
        h.tailExp_lt
      have htailExpLt :
          eval tailExp < eval exp :=
        rawLT_sound tailExp exp htailExpNormal hexpNormal htailExpRawLT
      have hinner :
          eval tailTail <
            (Ordinal.omega0 : Ordinal.{0}) ^ eval tailExp :=
        eval_tail_lt_leadingPower_of_normal
          tailExp tailCoeff tailTail htailNormal
      exact
        eval_cnf_lt_opow_of_tail_lt tailCoeff hinner htailExpLt
termination_by structural tail

/--
Strict raw comparison is semantically sound on normal ε₀ terms.
-/
theorem rawLT_sound
    (a b : E0Term)
    (ha : IsNormal a) (hb : IsNormal b)
    (hlt : RawLT a b) :
    eval a < eval b := by
  cases a with
  | zero =>
      cases b with
      | zero =>
          simp [RawLT, compareRaw] at hlt
      | cnf exp' coeff' tail' =>
          simpa using eval_cnf_pos exp' coeff' tail'
  | cnf exp coeff tail =>
      cases b with
      | zero =>
          simp [RawLT, compareRaw] at hlt
      | cnf exp' coeff' tail' =>
          have htail :
              eval tail <
                (Ordinal.omega0 : Ordinal.{0}) ^ eval exp :=
            eval_tail_lt_leadingPower_of_normal exp coeff tail ha
          rcases
              (rawLT_cnf_iff exp exp' coeff coeff' tail tail').1 hlt with
            hExp | ⟨hExpEq, hCoeff⟩
          · have hExpSem :
                eval exp < eval exp' :=
              rawLT_sound exp exp' ha.exp hb.exp hExp
            exact
              eval_cnf_lt_of_exp_lt coeff coeff' htail hExpSem
          · subst exp'
            rcases hCoeff with hCoeffLt | ⟨hCoeffEq, hTail⟩
            · exact eval_cnf_lt_of_coeff_lt htail hCoeffLt
            · subst coeff'
              have hTailSem :
                  eval tail < eval tail' :=
                rawLT_sound tail tail' ha.tail hb.tail hTail
              exact eval_cnf_lt_of_tail_lt hTailSem
termination_by structural a

/--
Strict semantic comparison of normal ε₀ terms is detected by the raw comparator.
-/
theorem rawLT_complete
    (a b : E0Term)
    (ha : IsNormal a) (hb : IsNormal b)
    (hsem : eval a < eval b) :
    RawLT a b := by
  cases hcmp : compareRaw a b with
  | lt =>
      exact hcmp
  | eq =>
      have hab : a = b :=
        (compareRaw_eq_eq_iff a b).1 hcmp
      subst b
      exact False.elim ((lt_irrefl _) hsem)
  | gt =>
      have hrev : RawLT b a :=
        (compareRaw_eq_gt_iff_reverse_rawLT a b).1 hcmp
      have hrevSem : eval b < eval a :=
        rawLT_sound b a hb ha hrev
      exact False.elim ((lt_asymm hsem) hrevSem)

/-- On normal raw terms, syntactic and semantic strict comparison agree. -/
theorem rawLT_iff_eval_lt
    (a b : E0Term)
    (ha : IsNormal a) (hb : IsNormal b) :
    RawLT a b ↔ eval a < eval b := by
  constructor
  · exact rawLT_sound a b ha hb
  · exact rawLT_complete a b ha hb

end

end E0Term

namespace E0

/-- Canonical ε₀ order agrees exactly with ordinal comparison under evaluation. -/
theorem lt_iff_eval_lt (a b : E0) :
    a < b ↔ eval a < eval b := by
  change E0Term.RawLT a.1 b.1 ↔ E0Term.eval a.1 < E0Term.eval b.1
  exact E0Term.rawLT_iff_eval_lt a.1 b.1 a.2 b.2

end E0
end OrdinalAnalysis
