import OrdinalAnalysis.Epsilon0.SemanticBounds

/-!
# One-step semantic comparison for ε₀ CNF nodes

This file isolates the ordinal arithmetic behind the three lexicographic
branches of the raw ε₀ comparator.

The lemmas are deliberately conditional: recursive comparison correctness and
normal-tail bounds will later supply their hypotheses.
-/

namespace OrdinalAnalysis
namespace E0Term

/--
If the source tail is below its leading power and the source exponent evaluates
strictly below the target exponent, then the whole source CNF node evaluates
strictly below the target node.
-/
theorem eval_cnf_lt_of_exp_lt
    {exp exp' tail tail' : E0Term} (coeff coeff' : Nat)
    (htail :
      eval tail < (Ordinal.omega0 : Ordinal.{0}) ^ eval exp)
    (hexp : eval exp < eval exp') :
    eval (.cnf exp coeff tail) <
      eval (.cnf exp' coeff' tail') := by
  have hsource :
      eval (.cnf exp coeff tail) <
        (Ordinal.omega0 : Ordinal.{0}) ^ eval exp' :=
    eval_cnf_lt_opow_of_tail_lt coeff htail hexp
  have hcoeffPos : 0 < (coeff'.succ : Ordinal.{0}) := by
    simp
  have hpow_le_block :
      (Ordinal.omega0 : Ordinal.{0}) ^ eval exp' ≤
        (Ordinal.omega0 : Ordinal.{0}) ^ eval exp' *
          (coeff'.succ : Ordinal.{0}) :=
    Ordinal.le_mul_left _ hcoeffPos
  exact
    hsource.trans_le
      (hpow_le_block.trans (leadingBlock_le_eval exp' coeff' tail'))

/--
At a common exponent, a strictly smaller finite coefficient makes the whole
source node smaller, provided its tail lies below the common leading power.
-/
theorem eval_cnf_lt_of_coeff_lt
    {exp tail tail' : E0Term} {coeff coeff' : Nat}
    (htail :
      eval tail < (Ordinal.omega0 : Ordinal.{0}) ^ eval exp)
    (hcoeff : coeff < coeff') :
    eval (.cnf exp coeff tail) <
      eval (.cnf exp coeff' tail') := by
  rw [eval_cnf, eval_cnf]
  have hcoeff' :
      (coeff.succ : Ordinal.{0}) < (coeff'.succ : Ordinal.{0}) := by
    exact_mod_cast Nat.succ_lt_succ hcoeff
  exact
    (Ordinal.opow_mul_add_lt_opow_mul htail hcoeff').trans_le le_self_add

/--
At a common exponent and coefficient, strict semantic comparison of the tails
lifts directly to strict comparison of the full CNF nodes.
-/
theorem eval_cnf_lt_of_tail_lt
    {exp tail tail' : E0Term} {coeff : Nat}
    (htail : eval tail < eval tail') :
    eval (.cnf exp coeff tail) <
      eval (.cnf exp coeff tail') := by
  rw [eval_cnf, eval_cnf]
  exact (add_lt_add_iff_left _).2 htail

end E0Term
end OrdinalAnalysis
