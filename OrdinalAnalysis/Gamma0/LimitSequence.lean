import OrdinalAnalysis.Generic.Classifier
import OrdinalAnalysis.Gamma0.NotationSystem

/-!
# Certified limit-sequence data for Γ₀

A sequence certificate can be constructed independently of a total classifier.
Its fields match the generic classifier's limit specification. Supremum
convergence is derived once for all future concrete Γ₀ sequence constructions.
-/

namespace OrdinalAnalysis
namespace G0

/-- An increasing, bounded, cofinal sequence at a canonical limit notation. -/
structure LimitSequenceData (a : G0) where
  seq : Nat → G0
  isSuccLimit : Order.IsSuccLimit (eval a)
  strictMono : StrictMono seq
  lt : ∀ n, seq n < a
  cofinal : ∀ α, α < eval a → ∃ n, α < eval (seq n)

/-- Every certified sequence converges semantically to its input notation. -/
theorem LimitSequenceData.iSup_eval {a : G0} (data : LimitSequenceData a) :
    (⨆ n, eval (data.seq n)) = eval a := by
  apply le_antisymm
  · apply Ordinal.iSup_le
    intro n
    exact ((lt_iff_eval_lt _ _).1 (data.lt n)).le
  · apply le_of_not_gt
    intro h
    obtain ⟨n, hn⟩ := data.cofinal _ h
    exact (not_lt_of_ge (Ordinal.le_iSup _ n)) hn

/-- A sequence certificate supplies the generic limit-branch specification. -/
theorem LimitSequenceData.satisfies {a : G0} (data : LimitSequenceData a) :
    (ClassificationResult.limit data.seq).Satisfies notationSystem a := by
  change Order.IsSuccLimit (eval a) ∧
    (∀ n, data.seq n < data.seq (n + 1) ∧ data.seq n < a) ∧
    ∀ α, α < eval a → ∃ n, α < eval (data.seq n)
  exact ⟨data.isSuccLimit,
    fun n => ⟨data.strictMono (Nat.lt_succ_self n), data.lt n⟩, data.cofinal⟩

end G0
end OrdinalAnalysis
