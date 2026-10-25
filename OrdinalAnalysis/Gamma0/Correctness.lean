import OrdinalAnalysis.Gamma0.SemanticCompare
import Mathlib.Tactic

/-!
# Correctness of Γ₀ raw comparison

The executable raw comparator is proved to agree exactly with mathlib ordinal
comparison on Veblen-normal-form terms.

The proof proceeds in two stages:

1. comparison is correct for terms satisfying the semantic recursive tail-bound
   invariant `HasSemanticTailBounds`;
2. executable normality implies that invariant.

This avoids a circular proof: tail bounds for a normal sum use comparison
correctness for its two leading principal terms, while comparator correctness
itself only assumes the tail bounds already hold.
-/

namespace OrdinalAnalysis
namespace G0Term

open Ordinal

/--
Under semantic recursive tail bounds, the executable raw comparator agrees
exactly with ordinal `cmp`.
-/
theorem compareRaw_eq_cmp_eval
    (a b : G0Term)
    (ha : HasSemanticTailBounds a)
    (hb : HasSemanticTailBounds b) :
    compareRaw a b = cmp (eval a) (eval b) := by
  cases a with
  | zero =>
      cases b with
      | zero =>
          simp [compareRaw]
      | veblen index' arg' coeff' tail' =>
          have hpos : 0 < eval (.veblen index' arg' coeff' tail') :=
            eval_veblen_pos index' arg' coeff' tail'
          rw [compareRaw]
          exact ((cmp_eq_lt_iff _ _).2 hpos).symm
  | veblen index arg coeff tail =>
      cases b with
      | zero =>
          have hpos : 0 < eval (.veblen index arg coeff tail) :=
            eval_veblen_pos index arg coeff tail
          rw [compareRaw]
          exact ((cmp_eq_gt_iff _ _).2 hpos).symm
      | veblen index' arg' coeff' tail' =>
          have hIndex :=
            compareRaw_eq_cmp_eval index index' ha.index hb.index
          cases hIndexRaw : compareRaw index index' with
          | eq =>
              have hIndexSem :
                  cmp (eval index) (eval index') = .eq := by
                rw [← hIndex]
                exact hIndexRaw
              have hPrincipal :
                  compareRaw arg arg' =
                    cmp
                      (Ordinal.veblen (eval index) (eval arg))
                      (Ordinal.veblen (eval index') (eval arg')) := by
                rw [Ordinal.cmp_veblen, hIndexSem]
                exact
                  compareRaw_eq_cmp_eval arg arg' ha.arg hb.arg
              cases hPrincipalRaw : compareRaw arg arg' with
              | lt =>
                  have hPrincipalSem :
                      Ordinal.veblen (eval index) (eval arg) <
                        Ordinal.veblen (eval index') (eval arg') := by
                    apply (cmp_eq_lt_iff _ _).1
                    rw [← hPrincipal]
                    exact hPrincipalRaw
                  have hsem :=
                    eval_veblen_lt_of_principal_lt coeff coeff'
                      ha.tail_lt_principal hPrincipalSem
                  rw [compareRaw, hIndexRaw, hPrincipalRaw]
                  exact ((cmp_eq_lt_iff _ _).2 hsem).symm
              | gt =>
                  have hPrincipalSem :
                      Ordinal.veblen (eval index') (eval arg') <
                        Ordinal.veblen (eval index) (eval arg) := by
                    apply (cmp_eq_gt_iff _ _).1
                    rw [← hPrincipal]
                    exact hPrincipalRaw
                  have hsem :=
                    eval_veblen_lt_of_principal_lt coeff' coeff
                      hb.tail_lt_principal hPrincipalSem
                  rw [compareRaw, hIndexRaw, hPrincipalRaw]
                  exact ((cmp_eq_gt_iff _ _).2 hsem).symm
              | eq =>
                  have hPrincipalEq :
                      Ordinal.veblen (eval index) (eval arg) =
                        Ordinal.veblen (eval index') (eval arg') := by
                    apply (cmp_eq_eq_iff _ _).1
                    rw [← hPrincipal]
                    exact hPrincipalRaw
                  cases hCoeff : compare coeff coeff' with
                  | lt =>
                      have hCoeffLt : coeff < coeff' :=
                        Nat.compare_eq_lt.mp hCoeff
                      rw [compareRaw, hIndexRaw, hPrincipalRaw, hCoeff]
                      apply ((cmp_eq_lt_iff _ _).2 ?_).symm
                      rw [← hPrincipalEq]
                      exact
                        eval_veblen_lt_of_coeff_lt
                          ha.tail_lt_principal hCoeffLt
                  | gt =>
                      have hCoeffLt : coeff' < coeff :=
                        Nat.compare_eq_gt.mp hCoeff
                      rw [compareRaw, hIndexRaw, hPrincipalRaw, hCoeff]
                      apply ((cmp_eq_gt_iff _ _).2 ?_).symm
                      rw [← hPrincipalEq]
                      exact
                        eval_veblen_lt_of_coeff_lt
                          hb.tail_lt_principal hCoeffLt
                  | eq =>
                      have hCoeffEq : coeff = coeff' :=
                        Nat.compare_eq_eq.mp hCoeff
                      subst coeff'
                      have hTail :=
                        compareRaw_eq_cmp_eval tail tail' ha.tail hb.tail
                      cases hTailRaw : compareRaw tail tail' with
                      | lt =>
                          have hTailSem : eval tail < eval tail' := by
                            apply (cmp_eq_lt_iff _ _).1
                            rw [← hTail]
                            exact hTailRaw
                          rw [compareRaw, hIndexRaw, hPrincipalRaw, hCoeff, hTailRaw]
                          apply ((cmp_eq_lt_iff _ _).2 ?_).symm
                          rw [← hPrincipalEq]
                          exact eval_veblen_lt_of_tail_lt hTailSem
                      | gt =>
                          have hTailSem : eval tail' < eval tail := by
                            apply (cmp_eq_gt_iff _ _).1
                            rw [← hTail]
                            exact hTailRaw
                          rw [compareRaw, hIndexRaw, hPrincipalRaw, hCoeff, hTailRaw]
                          apply ((cmp_eq_gt_iff _ _).2 ?_).symm
                          rw [← hPrincipalEq]
                          exact eval_veblen_lt_of_tail_lt hTailSem
                      | eq =>
                          have hTailEq : eval tail = eval tail' := by
                            apply (cmp_eq_eq_iff _ _).1
                            rw [← hTail]
                            exact hTailRaw
                          rw [compareRaw, hIndexRaw, hPrincipalRaw, hCoeff, hTailRaw]
                          apply (cmp_eq_eq_iff _ _).2
                          simp [eval_veblen, hPrincipalEq, hTailEq]
          | lt =>
              have hIndexSem :
                  cmp (eval index) (eval index') = .lt := by
                rw [← hIndex]
                exact hIndexRaw
              have hTargetPrincipal :
                  HasSemanticTailBounds (principal index' arg') :=
                HasSemanticTailBounds.principal hb.index hb.arg
              have hRecursive :=
                compareRaw_eq_cmp_eval arg (principal index' arg')
                  ha.arg hTargetPrincipal
              have hPrincipal :
                  compareRaw arg (principal index' arg') =
                    cmp
                      (Ordinal.veblen (eval index) (eval arg))
                      (Ordinal.veblen (eval index') (eval arg')) := by
                rw [Ordinal.cmp_veblen, hIndexSem]
                simpa using hRecursive
              cases hPrincipalRaw : compareRaw arg (principal index' arg') with
              | lt =>
                  have hPrincipalSem :
                      Ordinal.veblen (eval index) (eval arg) <
                        Ordinal.veblen (eval index') (eval arg') := by
                    apply (cmp_eq_lt_iff _ _).1
                    rw [← hPrincipal]
                    exact hPrincipalRaw
                  have hsem :=
                    eval_veblen_lt_of_principal_lt coeff coeff'
                      ha.tail_lt_principal hPrincipalSem
                  rw [compareRaw, hIndexRaw, hPrincipalRaw]
                  exact ((cmp_eq_lt_iff _ _).2 hsem).symm
              | gt =>
                  have hPrincipalSem :
                      Ordinal.veblen (eval index') (eval arg') <
                        Ordinal.veblen (eval index) (eval arg) := by
                    apply (cmp_eq_gt_iff _ _).1
                    rw [← hPrincipal]
                    exact hPrincipalRaw
                  have hsem :=
                    eval_veblen_lt_of_principal_lt coeff' coeff
                      hb.tail_lt_principal hPrincipalSem
                  rw [compareRaw, hIndexRaw, hPrincipalRaw]
                  exact ((cmp_eq_gt_iff _ _).2 hsem).symm
              | eq =>
                  have hPrincipalEq :
                      Ordinal.veblen (eval index) (eval arg) =
                        Ordinal.veblen (eval index') (eval arg') := by
                    apply (cmp_eq_eq_iff _ _).1
                    rw [← hPrincipal]
                    exact hPrincipalRaw
                  cases hCoeff : compare coeff coeff' with
                  | lt =>
                      have hCoeffLt : coeff < coeff' :=
                        Nat.compare_eq_lt.mp hCoeff
                      rw [compareRaw, hIndexRaw, hPrincipalRaw, hCoeff]
                      apply ((cmp_eq_lt_iff _ _).2 ?_).symm
                      rw [← hPrincipalEq]
                      exact
                        eval_veblen_lt_of_coeff_lt
                          ha.tail_lt_principal hCoeffLt
                  | gt =>
                      have hCoeffLt : coeff' < coeff :=
                        Nat.compare_eq_gt.mp hCoeff
                      rw [compareRaw, hIndexRaw, hPrincipalRaw, hCoeff]
                      apply ((cmp_eq_gt_iff _ _).2 ?_).symm
                      rw [← hPrincipalEq]
                      exact
                        eval_veblen_lt_of_coeff_lt
                          hb.tail_lt_principal hCoeffLt
                  | eq =>
                      have hCoeffEq : coeff = coeff' :=
                        Nat.compare_eq_eq.mp hCoeff
                      subst coeff'
                      have hTail :=
                        compareRaw_eq_cmp_eval tail tail' ha.tail hb.tail
                      cases hTailRaw : compareRaw tail tail' with
                      | lt =>
                          have hTailSem : eval tail < eval tail' := by
                            apply (cmp_eq_lt_iff _ _).1
                            rw [← hTail]
                            exact hTailRaw
                          rw [compareRaw, hIndexRaw, hPrincipalRaw, hCoeff, hTailRaw]
                          apply ((cmp_eq_lt_iff _ _).2 ?_).symm
                          rw [← hPrincipalEq]
                          exact eval_veblen_lt_of_tail_lt hTailSem
                      | gt =>
                          have hTailSem : eval tail' < eval tail := by
                            apply (cmp_eq_gt_iff _ _).1
                            rw [← hTail]
                            exact hTailRaw
                          rw [compareRaw, hIndexRaw, hPrincipalRaw, hCoeff, hTailRaw]
                          apply ((cmp_eq_gt_iff _ _).2 ?_).symm
                          rw [← hPrincipalEq]
                          exact eval_veblen_lt_of_tail_lt hTailSem
                      | eq =>
                          have hTailEq : eval tail = eval tail' := by
                            apply (cmp_eq_eq_iff _ _).1
                            rw [← hTail]
                            exact hTailRaw
                          rw [compareRaw, hIndexRaw, hPrincipalRaw, hCoeff, hTailRaw]
                          apply (cmp_eq_eq_iff _ _).2
                          simp [eval_veblen, hPrincipalEq, hTailEq]
          | gt =>
              have hIndexSem :
                  cmp (eval index) (eval index') = .gt := by
                rw [← hIndex]
                exact hIndexRaw
              have hSourcePrincipal :
                  HasSemanticTailBounds (principal index arg) :=
                HasSemanticTailBounds.principal ha.index ha.arg
              have hRecursive :=
                compareRaw_eq_cmp_eval (principal index arg) arg'
                  hSourcePrincipal hb.arg
              have hPrincipal :
                  compareRaw (principal index arg) arg' =
                    cmp
                      (Ordinal.veblen (eval index) (eval arg))
                      (Ordinal.veblen (eval index') (eval arg')) := by
                rw [Ordinal.cmp_veblen, hIndexSem]
                simpa using hRecursive
              cases hPrincipalRaw : compareRaw (principal index arg) arg' with
              | lt =>
                  have hPrincipalSem :
                      Ordinal.veblen (eval index) (eval arg) <
                        Ordinal.veblen (eval index') (eval arg') := by
                    apply (cmp_eq_lt_iff _ _).1
                    rw [← hPrincipal]
                    exact hPrincipalRaw
                  have hsem :=
                    eval_veblen_lt_of_principal_lt coeff coeff'
                      ha.tail_lt_principal hPrincipalSem
                  rw [compareRaw, hIndexRaw, hPrincipalRaw]
                  exact ((cmp_eq_lt_iff _ _).2 hsem).symm
              | gt =>
                  have hPrincipalSem :
                      Ordinal.veblen (eval index') (eval arg') <
                        Ordinal.veblen (eval index) (eval arg) := by
                    apply (cmp_eq_gt_iff _ _).1
                    rw [← hPrincipal]
                    exact hPrincipalRaw
                  have hsem :=
                    eval_veblen_lt_of_principal_lt coeff' coeff
                      hb.tail_lt_principal hPrincipalSem
                  rw [compareRaw, hIndexRaw, hPrincipalRaw]
                  exact ((cmp_eq_gt_iff _ _).2 hsem).symm
              | eq =>
                  have hPrincipalEq :
                      Ordinal.veblen (eval index) (eval arg) =
                        Ordinal.veblen (eval index') (eval arg') := by
                    apply (cmp_eq_eq_iff _ _).1
                    rw [← hPrincipal]
                    exact hPrincipalRaw
                  cases hCoeff : compare coeff coeff' with
                  | lt =>
                      have hCoeffLt : coeff < coeff' :=
                        Nat.compare_eq_lt.mp hCoeff
                      rw [compareRaw, hIndexRaw, hPrincipalRaw, hCoeff]
                      apply ((cmp_eq_lt_iff _ _).2 ?_).symm
                      rw [← hPrincipalEq]
                      exact
                        eval_veblen_lt_of_coeff_lt
                          ha.tail_lt_principal hCoeffLt
                  | gt =>
                      have hCoeffLt : coeff' < coeff :=
                        Nat.compare_eq_gt.mp hCoeff
                      rw [compareRaw, hIndexRaw, hPrincipalRaw, hCoeff]
                      apply ((cmp_eq_gt_iff _ _).2 ?_).symm
                      rw [← hPrincipalEq]
                      exact
                        eval_veblen_lt_of_coeff_lt
                          hb.tail_lt_principal hCoeffLt
                  | eq =>
                      have hCoeffEq : coeff = coeff' :=
                        Nat.compare_eq_eq.mp hCoeff
                      subst coeff'
                      have hTail :=
                        compareRaw_eq_cmp_eval tail tail' ha.tail hb.tail
                      cases hTailRaw : compareRaw tail tail' with
                      | lt =>
                          have hTailSem : eval tail < eval tail' := by
                            apply (cmp_eq_lt_iff _ _).1
                            rw [← hTail]
                            exact hTailRaw
                          rw [compareRaw, hIndexRaw, hPrincipalRaw, hCoeff, hTailRaw]
                          apply ((cmp_eq_lt_iff _ _).2 ?_).symm
                          rw [← hPrincipalEq]
                          exact eval_veblen_lt_of_tail_lt hTailSem
                      | gt =>
                          have hTailSem : eval tail' < eval tail := by
                            apply (cmp_eq_gt_iff _ _).1
                            rw [← hTail]
                            exact hTailRaw
                          rw [compareRaw, hIndexRaw, hPrincipalRaw, hCoeff, hTailRaw]
                          apply ((cmp_eq_gt_iff _ _).2 ?_).symm
                          rw [← hPrincipalEq]
                          exact eval_veblen_lt_of_tail_lt hTailSem
                      | eq =>
                          have hTailEq : eval tail = eval tail' := by
                            apply (cmp_eq_eq_iff _ _).1
                            rw [← hTail]
                            exact hTailRaw
                          rw [compareRaw, hIndexRaw, hPrincipalRaw, hCoeff, hTailRaw]
                          apply (cmp_eq_eq_iff _ _).2
                          simp [eval_veblen, hPrincipalEq, hTailEq]
termination_by a b => a.nodeCount + b.nodeCount
decreasing_by
  all_goals
    simp_all [nodeCount, principal]
    have hindex := nodeCount_pos index
    have harg := nodeCount_pos arg
    have htail := nodeCount_pos tail
    have hindex' := nodeCount_pos index'
    have harg' := nodeCount_pos arg'
    have htail' := nodeCount_pos tail'
    omega

/-- Executable Veblen normality implies all recursive semantic tail bounds. -/
theorem hasSemanticTailBounds_of_normal
    (t : G0Term) (h : IsNormal t) :
    HasSemanticTailBounds t := by
  induction t with
  | zero =>
      trivial
  | veblen index arg coeff tail ihIndex ihArg ihTail =>
      have hindexNormal := h.index
      have hargNormal := h.arg
      have htailNormal := h.tail
      have hindexBounds := ihIndex hindexNormal
      have hargBounds := ihArg hargNormal
      have htailBounds := ihTail htailNormal
      refine ⟨hindexBounds, hargBounds, htailBounds, ?_⟩
      cases tail with
      | zero =>
          simp
      | veblen tailIndex tailArg tailCoeff tailTail =>
          have htailPrincipalRaw :
              RawLT
                (principal tailIndex tailArg)
                (principal index arg) :=
            h.tailPrincipal_lt
          have htailIndexBounds : HasSemanticTailBounds tailIndex :=
            htailBounds.index
          have htailArgBounds : HasSemanticTailBounds tailArg :=
            htailBounds.arg
          have hleft :
              HasSemanticTailBounds (principal tailIndex tailArg) :=
            HasSemanticTailBounds.principal
              htailIndexBounds htailArgBounds
          have hright :
              HasSemanticTailBounds (principal index arg) :=
            HasSemanticTailBounds.principal hindexBounds hargBounds
          have hcmp :=
            compareRaw_eq_cmp_eval
              (principal tailIndex tailArg)
              (principal index arg) hleft hright
          have hprincipalSem :
              eval (principal tailIndex tailArg) <
                eval (principal index arg) := by
            apply (cmp_eq_lt_iff _ _).1
            rw [← hcmp]
            exact htailPrincipalRaw
          exact
            eval_veblen_lt_principal_of_principal_lt tailCoeff
              htailBounds.tail_lt_principal
              (by simpa using hprincipalSem)

/-- On normal raw terms, the executable comparator agrees exactly with ordinal `cmp`. -/
theorem compareRaw_eq_cmp_eval_of_normal
    (a b : G0Term)
    (ha : IsNormal a) (hb : IsNormal b) :
    compareRaw a b = cmp (eval a) (eval b) :=
  compareRaw_eq_cmp_eval a b
    (hasSemanticTailBounds_of_normal a ha)
    (hasSemanticTailBounds_of_normal b hb)

/-- Strict raw comparison is semantically sound and complete on normal Γ₀ terms. -/
theorem rawLT_iff_eval_lt
    (a b : G0Term)
    (ha : IsNormal a) (hb : IsNormal b) :
    RawLT a b ↔ eval a < eval b := by
  rw [RawLT, compareRaw_eq_cmp_eval_of_normal a b ha hb, cmp_eq_lt_iff]

end G0Term

namespace G0

/-- Canonical Γ₀ order agrees exactly with ordinal comparison under evaluation. -/
theorem lt_iff_eval_lt (a b : G0) :
    a < b ↔ eval a < eval b := by
  change G0Term.RawLT a.1 b.1 ↔ G0Term.eval a.1 < G0Term.eval b.1
  exact G0Term.rawLT_iff_eval_lt a.1 b.1 a.2 b.2

end G0
end OrdinalAnalysis
