import OrdinalAnalysis.Gamma0.Predecessor

/-!
# Executable Γ₀ successor-view examples

Exercise both finite predecessor branches, descent through a nonzero tail,
and limit blocks with zero and nonzero Veblen index.
-/

namespace OrdinalAnalysis
namespace Examples

private def two : G0 :=
  ⟨.veblen .zero .zero 1 .zero, by native_decide⟩

private def omegaPlusOne : G0 :=
  ⟨.veblen .zero G0Term.one 0 G0Term.one, by native_decide⟩

private def omegaTwice : G0 :=
  ⟨.veblen .zero G0Term.one 1 .zero, by native_decide⟩

example : G0.successorView G0.zero = .zero := by native_decide
example : G0.predecessor? G0.one = some G0.zero := by native_decide
example : G0.predecessor? two = some G0.one := by native_decide
example : G0.predecessor? omegaPlusOne = some G0.omega := by native_decide
example : G0.successorView G0.omega = .limit := by native_decide
example : G0.successorView omegaTwice = .limit := by native_decide
example : G0.successorView G0.epsilonZero = .limit := by native_decide

example : Order.IsSuccLimit (G0.eval G0.epsilonZero) := by
  have h := G0.successorView_has_prop G0.epsilonZero
  have hv : G0.successorView G0.epsilonZero = .limit := by native_decide
  simpa only [hv, G0.SuccessorView.Satisfies] using h

example (a p : G0) (h : G0.predecessor? a = some p) :
    G0.eval a = Order.succ (G0.eval p) ∧ p < a :=
  ⟨G0.predecessor?_sound h, G0.predecessor?_lt h⟩

end Examples
end OrdinalAnalysis
