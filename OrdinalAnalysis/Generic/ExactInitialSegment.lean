import OrdinalAnalysis.Generic.OrdinalNotationSystem
import Mathlib.Order.Hom.Set

/-!
# Exact initial-segment theory for ordinal notation systems

Completeness and order correctness imply that every `OrdinalNotationSystem`
is not merely embedded in the ordinals: its semantic range is exactly the
initial segment below its declared bound.

This file derives that fact once and packages semantic evaluation as an order
isomorphism onto `Set.Iio system.bound`.
-/

namespace OrdinalAnalysis
namespace OrdinalNotationSystem

universe u

variable {N : Type u} [LinearOrder N]

/-- Membership in the semantic range is exactly the condition of lying below the bound. -/
theorem mem_range_eval_iff
    (system : OrdinalNotationSystem N) {α : Ordinal} :
    α ∈ Set.range system.eval ↔ α < system.bound := by
  constructor
  · rintro ⟨a, rfl⟩
    exact system.eval_lt_bound a
  · intro hα
    exact system.complete hα

/-- The semantic range is exactly the initial segment below the system bound. -/
theorem range_eval_eq_Iio
    (system : OrdinalNotationSystem N) :
    Set.range system.eval = Set.Iio system.bound := by
  ext α
  simpa only [Set.mem_range, Set.mem_Iio] using
    (system.mem_range_eval_iff (α := α))

/-- Evaluation with its proof that every value lies below the system bound. -/
def toIio (system : OrdinalNotationSystem N) :
    N → Set.Iio system.bound :=
  fun a => ⟨system.eval a, system.eval_lt_bound a⟩

@[simp]
theorem toIio_coe
    (system : OrdinalNotationSystem N) (a : N) :
    (system.toIio a : Ordinal) = system.eval a :=
  rfl

/-- The canonical map into the represented initial segment is strictly monotone. -/
theorem toIio_strictMono
    (system : OrdinalNotationSystem N) :
    StrictMono system.toIio := by
  intro a b hab
  exact system.eval_strictMono hab

/-- Completeness makes the canonical map onto the represented initial segment surjective. -/
theorem toIio_surjective
    (system : OrdinalNotationSystem N) :
    Function.Surjective system.toIio := by
  intro α
  obtain ⟨a, ha⟩ := system.complete α.2
  refine ⟨a, ?_⟩
  apply Subtype.ext
  exact ha

/--
Every verified notation system is order-isomorphic to the ordinal initial
segment below its declared bound.
-/
noncomputable def orderIsoIio
    (system : OrdinalNotationSystem N) :
    N ≃o Set.Iio system.bound :=
  StrictMono.orderIsoOfSurjective
    system.toIio system.toIio_strictMono system.toIio_surjective

@[simp]
theorem orderIsoIio_apply_coe
    (system : OrdinalNotationSystem N) (a : N) :
    (system.orderIsoIio a : Ordinal) = system.eval a := by
  rfl

end OrdinalNotationSystem
end OrdinalAnalysis
