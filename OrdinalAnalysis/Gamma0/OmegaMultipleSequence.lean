import OrdinalAnalysis.Gamma0.FiniteBlocks
import OrdinalAnalysis.Gamma0.LimitSequence

/-!
# Executable fundamental sequences for finite multiples of ω

For every natural k, the sequence ω · k + n is strictly increasing and
cofinal below ω · (k + 1). The entries are built directly in finite syntax.
General Veblen limit sequences remain a later extension.
-/

namespace OrdinalAnalysis
namespace G0

open Ordinal

/-- The sequence n ↦ ω · k + n approaching the next multiple of ω. -/
def omegaMultipleSequence (k : Nat) : Nat → G0 :=
  omegaMulAddNat k

@[simp]
theorem eval_omegaMultipleSequence (k n : Nat) :
    eval (omegaMultipleSequence k n) =
      ω * (k : Ordinal.{0}) + (n : Ordinal.{0}) :=
  eval_omegaMulAddNat k n

theorem omegaMultipleSequence_strictMono (k : Nat) :
    StrictMono (omegaMultipleSequence k) := by
  intro m n hmn
  apply (lt_iff_eval_lt _ _).2
  rw [eval_omegaMultipleSequence, eval_omegaMultipleSequence]
  apply (add_lt_add_iff_left _).2
  exact_mod_cast hmn

theorem omegaMultipleSequence_lt (k n : Nat) :
    omegaMultipleSequence k n < omegaMultiple k.succ := by
  apply (lt_iff_eval_lt _ _).2
  rw [eval_omegaMultipleSequence, eval_omegaMultiple, Nat.cast_succ, mul_add_one]
  exact (add_lt_add_iff_left _).2 (Ordinal.natCast_lt_omega0 n)

theorem omegaMultipleSequence_cofinal (k : Nat) (α : Ordinal.{0})
    (hα : α < eval (omegaMultiple k.succ)) :
    ∃ n, α < eval (omegaMultipleSequence k n) := by
  rw [eval_omegaMultiple, Nat.cast_succ] at hα
  obtain ⟨d, hd, hle⟩ := Ordinal.lt_mul_add_one_iff.1 hα
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 hd
  refine ⟨n + 1, ?_⟩
  rw [eval_omegaMultipleSequence]
  apply hle.trans_lt
  apply (add_lt_add_iff_left _).2
  exact_mod_cast Nat.lt_succ_self n

/-- The first executable Γ₀ limit-sequence family, with all correctness fields. -/
def omegaMultipleLimitSequenceData (k : Nat) :
    LimitSequenceData (omegaMultiple k.succ) where
  seq := omegaMultipleSequence k
  isSuccLimit := by
    rw [eval_omegaMultiple]
    exact Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 (by simp)
  strictMono := omegaMultipleSequence_strictMono k
  lt := omegaMultipleSequence_lt k
  cofinal := omegaMultipleSequence_cofinal k

/-- Supremum convergence for every positive finite multiple of ω. -/
theorem omegaMultipleSequence_iSup_eval (k : Nat) :
    (⨆ n, eval (omegaMultipleSequence k n)) = eval (omegaMultiple k.succ) :=
  (omegaMultipleLimitSequenceData k).iSup_eval

/-- This family already satisfies the generic classifier's limit contract. -/
theorem omegaMultipleSequence_satisfies (k : Nat) :
    (ClassificationResult.limit (omegaMultipleSequence k)).Satisfies
      notationSystem (omegaMultiple k.succ) :=
  (omegaMultipleLimitSequenceData k).satisfies

end G0
end OrdinalAnalysis
