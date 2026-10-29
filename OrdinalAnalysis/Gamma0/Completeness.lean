import OrdinalAnalysis.Gamma0.SemanticNormalForm
import OrdinalAnalysis.Gamma0.VeblenDecomposition
import OrdinalAnalysis.Gamma0.BoundedEmbedding

/-!
# Completeness of canonical Γ₀ notations

Well-founded ordinal induction turns the decreasing semantic decomposition
into a normal finite term for every ordinal below Γ₀. The semantic constructor
lemma certifies the normality of the assembled node.

Together with soundness, this identifies the evaluation range exactly.
The chosen inverse is noncomputable; the finite syntax and comparator remain
the existing executable definitions.
-/

namespace OrdinalAnalysis

open Ordinal

namespace G0Term

/-- Every ordinal below Γ₀ is the evaluation of a normal finite raw term. -/
theorem exists_normal_eval_of_lt_gamma_zero (o : Ordinal.{0})
    (hbound : o < Γ₀) :
    ∃ t : G0Term, IsNormal t ∧ eval t = o := by
  revert hbound
  induction o using WellFoundedLT.induction with
  | ind o ih =>
      intro hbound
      by_cases hzero : o = 0
      · subst o
        exact ⟨.zero, isNormal_zero, rfl⟩
      · let d := Gamma0Decomposition.decompose o hzero hbound
        obtain ⟨index, hindex, eindex⟩ :=
          ih d.index d.index_lt (d.index_lt.trans hbound)
        obtain ⟨arg, harg, earg⟩ :=
          ih d.arg d.arg_lt (d.arg_lt.trans hbound)
        obtain ⟨tail, htail, etail⟩ :=
          ih d.tail d.tail_lt (d.tail_lt.trans hbound)
        refine ⟨.veblen index arg d.coeff tail, ?_, ?_⟩
        · apply isNormal_veblen_of_eval_bounds d.coeff hindex harg htail
          · rw [eindex, earg]
            exact d.arg_lt_principal
          · rw [eindex, earg, etail]
            exact d.tail_lt_principal
        · rw [eval_veblen, eindex, earg, etail]
          exact d.eval_eq

end G0Term

namespace G0

/-- Every ordinal below Γ₀ has a canonical notation. -/
theorem exists_eval_eq (o : Ordinal.{0}) (hbound : o < Γ₀) :
    ∃ a : G0, eval a = o := by
  obtain ⟨t, ht, heval⟩ := G0Term.exists_normal_eval_of_lt_gamma_zero o hbound
  exact ⟨⟨t, ht⟩, heval⟩

/-- Soundness and completeness identify the exact semantic range. -/
theorem range_eval_eq_Iio_gamma_zero :
    Set.range eval = Set.Iio (Γ₀ : Ordinal.{0}) := by
  apply Set.Subset.antisymm range_eval_subset_Iio_gamma_zero
  intro o ho
  exact exists_eval_eq o ho

/-- Choose the unique canonical notation for an ordinal below Γ₀. -/
noncomputable def ofOrdinal (o : Ordinal.{0}) (hbound : o < Γ₀) : G0 :=
  Classical.choose (exists_eval_eq o hbound)

/-- Evaluating the chosen notation returns its original ordinal. -/
@[simp]
theorem eval_ofOrdinal (o : Ordinal.{0}) (hbound : o < Γ₀) :
    eval (ofOrdinal o hbound) = o :=
  Classical.choose_spec (exists_eval_eq o hbound)

/-- Reconstructing a canonical notation from its value returns the same notation. -/
@[simp]
theorem ofOrdinal_eval (a : G0) :
    ofOrdinal (eval a) (eval_lt_gamma_zero a) = a := by
  apply eval_injective
  exact eval_ofOrdinal (eval a) (eval_lt_gamma_zero a)

/-- The bounded evaluation embedding is onto the entire initial segment below Γ₀. -/
theorem evalOrderEmbeddingIio_surjective :
    Function.Surjective evalOrderEmbeddingIio := by
  intro o
  obtain ⟨a, ha⟩ := exists_eval_eq o.1 o.2
  refine ⟨a, ?_⟩
  apply Subtype.ext
  exact ha

end G0
end OrdinalAnalysis
