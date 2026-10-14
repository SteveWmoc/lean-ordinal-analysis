import OrdinalAnalysis.Generic.ExactInitialSegment
import OrdinalAnalysis.Epsilon0.NotationSystem

/-!
# The ε₀ notation system as an exact ordinal initial segment

The generic exact-initial-segment theory specializes the completed ε₀ system
to an explicit order isomorphism with the ordinals below `ε₀`.
-/

namespace OrdinalAnalysis
namespace E0

open Ordinal

/-- Canonical ε₀ notations are order-isomorphic to the ordinals below `ε₀`. -/
noncomputable def orderIsoIioEpsilonZero :
    E0 ≃o Set.Iio ε₀ :=
  notationSystem.orderIsoIio

@[simp]
theorem orderIsoIioEpsilonZero_apply_coe (a : E0) :
    (orderIsoIioEpsilonZero a : Ordinal) = eval a :=
  rfl

end E0
end OrdinalAnalysis
