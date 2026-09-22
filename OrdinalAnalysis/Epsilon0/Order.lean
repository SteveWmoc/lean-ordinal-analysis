import OrdinalAnalysis.Epsilon0.NormalForm
import Mathlib.Order.Std

/-!
# Order on canonical ε₀ notations

Raw `E0Term` values carry only a certified structural comparator; they do not
receive global `<` and `≤` notation because raw syntax may be noncanonical.

The subtype `E0`, however, consists only of canonical Cantor normal forms.
Here we turn the certified structural comparator into a genuine decidable
linear order and transfer that order along the injective subtype projection.
-/

namespace OrdinalAnalysis

namespace E0

/--
The linear order on canonical ε₀ notations induced by structural comparison of
their underlying raw terms.

The temporary order on `E0Term` exists only while constructing this instance;
no global `LinearOrder E0Term` is installed.
-/
instance instLinearOrder : LinearOrder E0 := by
  letI : LinearOrder E0Term := .ofStd E0Term
  exact LinearOrder.lift' Subtype.val Subtype.val_injective

example : E0.zero < E0.one := by decide
example : E0.zero ≤ E0.one := by decide
example : ¬ E0.one < E0.zero := by decide
example : E0.zero ≠ E0.one := by decide

end E0

end OrdinalAnalysis
