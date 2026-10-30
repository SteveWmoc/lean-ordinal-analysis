import OrdinalAnalysis.Gamma0.SemanticNormalForm

/-!
# Finite blocks in Γ₀ syntax

Executable constructors for natural numbers and ordinals of the form
ω · m + n. They supply the first concrete limit-sequence entries.
-/

namespace OrdinalAnalysis
namespace G0Term

open Ordinal

/-- Raw notation for a natural number. -/
def natTerm : Nat → G0Term
  | 0 => .zero
  | n + 1 => .veblen .zero .zero n .zero

@[simp]
theorem eval_natTerm (n : Nat) : eval (natTerm n) = (n : Ordinal.{0}) := by
  cases n <;> simp [natTerm, Ordinal.veblen_zero_apply, Nat.cast_succ]

theorem isNormal_natTerm (n : Nat) : IsNormal (natTerm n) := by
  cases n <;> simp [natTerm, principal]

/-- Raw notation for ω · m + n, with no leading zero block. -/
def omegaMulAddNatTerm : Nat → Nat → G0Term
  | 0, n => natTerm n
  | m + 1, n => .veblen .zero one m (natTerm n)

@[simp]
theorem eval_omegaMulAddNatTerm (m n : Nat) :
    eval (omegaMulAddNatTerm m n) = ω * (m : Ordinal.{0}) + (n : Ordinal.{0}) := by
  cases m <;> simp [omegaMulAddNatTerm, Ordinal.veblen_zero_apply]

theorem isNormal_omegaMulAddNatTerm (m n : Nat) :
    IsNormal (omegaMulAddNatTerm m n) := by
  cases m with
  | zero =>
      exact isNormal_natTerm n
  | succ m =>
      apply isNormal_veblen_of_eval_bounds m isNormal_zero
        (show IsNormal one by native_decide) (isNormal_natTerm n)
      · simpa only [eval_zero, eval_one, Ordinal.veblen_zero_apply, Ordinal.opow_one]
          using Ordinal.one_lt_omega0
      · simpa only [eval_zero, eval_one, eval_natTerm,
          Ordinal.veblen_zero_apply, Ordinal.opow_one]
          using Ordinal.natCast_lt_omega0 n

end G0Term

namespace G0

open Ordinal

/-- Executable canonical notation for a natural number. -/
def ofNat (n : Nat) : G0 :=
  ⟨G0Term.natTerm n, G0Term.isNormal_natTerm n⟩

@[simp]
theorem eval_ofNat (n : Nat) : eval (ofNat n) = (n : Ordinal.{0}) :=
  G0Term.eval_natTerm n

/-- Executable canonical notation for ω · m + n. -/
def omegaMulAddNat (m n : Nat) : G0 :=
  ⟨G0Term.omegaMulAddNatTerm m n, G0Term.isNormal_omegaMulAddNatTerm m n⟩

@[simp]
theorem eval_omegaMulAddNat (m n : Nat) :
    eval (omegaMulAddNat m n) = ω * (m : Ordinal.{0}) + (n : Ordinal.{0}) :=
  G0Term.eval_omegaMulAddNatTerm m n

/-- Executable canonical notation for a finite multiple of ω, including zero. -/
def omegaMultiple (m : Nat) : G0 :=
  omegaMulAddNat m 0

@[simp]
theorem eval_omegaMultiple (m : Nat) :
    eval (omegaMultiple m) = ω * (m : Ordinal.{0}) := by
  simp only [omegaMultiple, eval_omegaMulAddNat, Nat.cast_zero, add_zero]

end G0
end OrdinalAnalysis
