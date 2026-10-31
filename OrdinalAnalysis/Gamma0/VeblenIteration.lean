import OrdinalAnalysis.Gamma0.VeblenApplication

/-!
# Executable Veblen iteration

Finite iteration reuses canonical Veblen application at every step, including
its fixed-point-collapse branch. Semantic correctness relates the executable
recursion to mathlib function iteration.
-/

namespace OrdinalAnalysis
namespace G0

/-- Iterate canonical Veblen application from a specified seed. -/
def veblenIterate (index seed : G0) : Nat → G0
  | 0 => seed
  | n + 1 => veblen index (veblenIterate index seed n)

@[simp]
theorem eval_veblenIterate (index seed : G0) (n : Nat) :
    eval (veblenIterate index seed n) =
      (Ordinal.veblen (eval index))^[n] (eval seed) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [veblenIterate, eval_veblen, ih, Function.iterate_succ_apply']

/-- Iteration is strictly increasing whenever the seed grows at the first step. -/
theorem veblenIterate_strictMono (index seed : G0)
    (hseed : seed < veblen index seed) :
    StrictMono (veblenIterate index seed) := by
  apply strictMono_nat_of_lt_succ
  intro n
  induction n with
  | zero => exact hseed
  | succ n ih => exact veblen_right_strictMono index ih

end G0
end OrdinalAnalysis
