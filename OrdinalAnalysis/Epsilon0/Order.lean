import OrdinalAnalysis.Epsilon0.NormalForm

/-!
# Strict comparison on canonical ε₀ notations

The raw datatype `E0Term` has an executable syntactic comparator but no global
order notation, because raw terms may be noncanonical.

For the canonical subtype `E0`, we expose that comparator as strict
comparison.  At this stage we intentionally install only `LT` and its
decision procedure.  The linear-order laws will be proved after the semantic
interpretation into `Ordinal` is available, by showing that this syntactic
comparison agrees with ordinal comparison.
-/

namespace OrdinalAnalysis
namespace E0

/-- Strict syntactic comparison of canonical ε₀ notations. -/
instance instLT : LT E0 where
  lt a b := E0Term.RawLT a.1 b.1

/-- Strict comparison of canonical ε₀ notations is decidable. -/
instance instDecidableLT (a b : E0) : Decidable (a < b) := by
  change Decidable (E0Term.compareRaw a.1 b.1 = .lt)
  exact decEq (E0Term.compareRaw a.1 b.1) .lt

example : E0.zero < E0.one := rfl
example : ¬ E0.one < E0.zero := by decide
example : E0.zero ≠ E0.one := by decide

end E0
end OrdinalAnalysis
