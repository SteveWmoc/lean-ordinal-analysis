import OrdinalAnalysis.Epsilon0.ExactInitialSegment
import OrdinalAnalysis.Epsilon0.Classifier
import OrdinalAnalysis.Generic.LimitSequence

/-!
# ε₀ examples for the generic notation-system API

These examples exercise the generic v0.3 API against the completed ε₀
implementation. They are compiled as part of the root library import so that
the documentation claim that ε₀ satisfies the generic interfaces remains
machine-checked.
-/

namespace OrdinalAnalysis
namespace E0

open Ordinal

/-- The generic notation-system adapter has the expected ε₀ bound. -/
example : notationSystem.bound = ε₀ :=
  rfl

/-- Generic order correctness specializes to the existing ε₀ semantics. -/
example (a b : E0) :
    a < b ↔ notationSystem.eval a < notationSystem.eval b :=
  notationSystem.lt_iff_eval_lt a b

/-- The generic exact-range theorem specializes to the ordinals below ε₀. -/
example :
    Set.range notationSystem.eval = Set.Iio ε₀ := by
  simpa using notationSystem.range_eval_eq_Iio

/-- The generic exact-initial-segment construction recovers the ε₀ order type. -/
noncomputable example :
    E0 ≃o Set.Iio ε₀ :=
  orderIsoIioEpsilonZero

/-- The existing ε₀ classifier satisfies the generic classifier contract. -/
example (a : E0) :
    (classifier.classify a).Satisfies notationSystem a :=
  classifier.classify_satisfies a

/-- The generic ergonomic API supplies a strictly increasing sequence at limits. -/
example (a : E0) (hlim : Order.IsSuccLimit (eval a)) :
    StrictMono (classifier.limitSequence a hlim) :=
  classifier.limitSequence_strictMono a hlim

/-- The same generic sequence is semantically convergent to the represented limit. -/
example (a : E0) (hlim : Order.IsSuccLimit (eval a)) :
    (⨆ i, eval (classifier.limitSequence a hlim i)) = eval a := by
  simpa using classifier.limitSequence_iSup_eval a hlim

end E0
end OrdinalAnalysis
