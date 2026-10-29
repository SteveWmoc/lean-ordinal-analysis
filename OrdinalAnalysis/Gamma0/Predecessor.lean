import OrdinalAnalysis.Gamma0.SuccessorView
import OrdinalAnalysis.Gamma0.LinearOrder

/-!
# Certified successor predecessors on canonical Γ₀ notations

This executable API distinguishes zero, successors, and limits. Successors
carry a canonical predecessor. Limits carry a semantic limit certificate;
fundamental sequences and the full generic classifier are later additions.
-/

namespace OrdinalAnalysis
namespace G0

open Ordinal Order

/-- Zero, a successor with its canonical predecessor, or a limit. -/
inductive SuccessorView where
  | zero
  | succ (predecessor : G0)
  | limit
deriving DecidableEq

/-- Semantic meaning of the canonical shape view. -/
def SuccessorView.Satisfies (a : G0) : SuccessorView → Prop
  | .zero => eval a = 0
  | .succ predecessor => eval a = succ (eval predecessor)
  | .limit => IsSuccLimit (eval a)

/-- The computed shape together with its semantic certificate. -/
structure SuccessorViewData (a : G0) where
  result : SuccessorView
  satisfies : result.Satisfies a

/-- Lift the raw classifier, using its normality proof for each predecessor. -/
def successorViewData (a : G0) : SuccessorViewData a := by
  have hprop := G0Term.successorView_satisfies a.1 a.2
  cases hv : G0Term.successorView a.1 with
  | zero =>
      refine ⟨.zero, ?_⟩
      simpa only [hv, G0Term.SuccessorView.Satisfies] using hprop
  | succ predecessor =>
      have hp : G0Term.IsNormal predecessor ∧
          G0Term.eval a.1 = succ (G0Term.eval predecessor) := by
        simpa only [hv, G0Term.SuccessorView.Satisfies] using hprop
      exact ⟨.succ ⟨predecessor, hp.1⟩, hp.2⟩
  | limit =>
      refine ⟨.limit, ?_⟩
      simpa only [hv, G0Term.SuccessorView.Satisfies] using hprop

/-- Executable zero/successor/limit classification on canonical Γ₀ terms. -/
def successorView (a : G0) : SuccessorView :=
  (successorViewData a).result

/-- Every computed case has its asserted semantic meaning. -/
theorem successorView_has_prop (a : G0) :
    (successorView a).Satisfies a :=
  (successorViewData a).satisfies

/-- Return a canonical predecessor exactly in the successor branch. -/
def predecessor? (a : G0) : Option G0 :=
  match successorView a with
  | .succ predecessor => some predecessor
  | _ => none

/-- Every returned predecessor has the required successor value. -/
theorem predecessor?_sound {a predecessor : G0}
    (h : predecessor? a = some predecessor) :
    eval a = succ (eval predecessor) := by
  unfold predecessor? at h
  cases hv : successorView a with
  | zero =>
      simp only [hv, Option.noConfusion] at h
  | limit =>
      simp only [hv, Option.noConfusion] at h
  | succ p =>
      have heq : p = predecessor := Option.some.inj (by simpa only [hv] using h)
      subst predecessor
      simpa only [hv, SuccessorView.Satisfies] using successorView_has_prop a

/-- A returned predecessor is strictly smaller than its input notation. -/
theorem predecessor?_lt {a predecessor : G0}
    (h : predecessor? a = some predecessor) : predecessor < a := by
  apply (lt_iff_eval_lt predecessor a).2
  calc
    eval predecessor < succ (eval predecessor) := lt_succ _
    _ = eval a := (predecessor?_sound h).symm

end G0
end OrdinalAnalysis
