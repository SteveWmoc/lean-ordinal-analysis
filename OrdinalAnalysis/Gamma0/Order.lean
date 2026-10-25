import OrdinalAnalysis.Gamma0.NormalForm

/-!
# Strict comparison on canonical Γ₀ notations

The raw datatype `G0Term` has an executable syntactic comparator but no global
order notation because raw terms may be noncanonical.

For the canonical subtype `G0`, this file exposes the raw comparator as strict
comparison. At this stage we intentionally install only `LT` and its decision
procedure. The order laws will be proved after semantic comparison correctness
has been established.
-/

namespace OrdinalAnalysis
namespace G0

/-- Strict syntactic comparison of canonical Γ₀ notations. -/
instance instLT : LT G0 where
  lt a b := G0Term.RawLT a.1 b.1

/-- Strict comparison of canonical Γ₀ notations is decidable. -/
instance instDecidableLT (a b : G0) : Decidable (a < b) := by
  change Decidable (G0Term.compareRaw a.1 b.1 = .lt)
  exact decEq (G0Term.compareRaw a.1 b.1) .lt

example : G0.zero < G0.one := by
  change G0Term.compareRaw G0Term.zero G0Term.one = .lt
  native_decide

example : G0.one < G0.omega := by
  change G0Term.compareRaw G0Term.one G0Term.omega = .lt
  native_decide

example : G0.omega < G0.epsilonZero := by
  change G0Term.compareRaw G0Term.omega G0Term.epsilonZero = .lt
  native_decide

end G0
end OrdinalAnalysis
