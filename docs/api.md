# API guide

This guide describes the detailed ε₀ API shipped through v0.3.0. The reusable generic notation-system API introduced in v0.3.0 is documented separately in [`generic-api.md`](generic-api.md).

The simplest import is:

```lean
import OrdinalAnalysis

open OrdinalAnalysis
```

The project intentionally distinguishes raw syntax, canonical syntax, executable comparison, and semantic interpretation.

## 1. Raw terms: `E0Term`

The raw datatype is:

```lean
inductive E0Term
  | zero
  | cnf (exp : E0Term) (coeff : Nat) (tail : E0Term)
```

A node

```lean
E0Term.cnf exp coeff tail
```

represents

```text
ω ^ exp * (coeff + 1) + tail
```

so the stored natural `coeff` is one less than the mathematical coefficient.

Useful structural operations include:

```lean
E0Term.one
E0Term.isZero
E0Term.leadingExponent?
E0Term.leadingCoefficient?
E0Term.tail?
E0Term.nodeCount
```

Raw terms need not be canonical.

## 2. Executable comparison

Raw comparison is defined directly on finite syntax:

```lean
E0Term.compareRaw : E0Term → E0Term → Ordering
E0Term.rawLT      : E0Term → E0Term → Bool
```

For example:

```lean
#eval E0Term.compareRaw E0Term.zero E0Term.one
```

The comparator is lexicographic on exponent, positive coefficient, and tail.

The proposition-level strict relation is:

```lean
E0Term.RawLT : E0Term → E0Term → Prop
```

Useful correctness statements include:

```lean
E0Term.compareRaw_eq_eq_iff
E0Term.rawLT_iff_eval_lt
```

The second theorem requires normal inputs.

## 3. Normal forms and `E0`

The executable normality checker is:

```lean
E0Term.isNormal : E0Term → Bool
```

The proof-facing proposition is:

```lean
E0Term.IsNormal : E0Term → Prop
```

Canonical notations are the subtype:

```lean
abbrev E0 := { t : E0Term // t.IsNormal }
```

Canonical zero and one are available as:

```lean
E0.zero
E0.one
```

After importing `OrdinalAnalysis`, `E0` also has `Zero` and `One` instances, so `(0 : E0)` and `(1 : E0)` may be used.

The main normal-form decomposition lemmas are:

```lean
E0Term.isNormal_cnf_iff
E0Term.IsNormal.exp
E0Term.IsNormal.tail
E0Term.IsNormal.tailExp_lt
```

## 4. Semantic interpretation

Raw semantics:

```lean
E0Term.eval : E0Term → Ordinal
```

Canonical semantics:

```lean
E0.eval : E0 → Ordinal
```

with defining behavior

```text
eval 0 = 0
eval (cnf exp coeff tail)
  = ω ^ eval exp * (coeff + 1) + eval tail.
```

The semantic maps are `noncomputable` because mathlib's abstract ordinal arithmetic is noncomputable. They are intended for specification and certification, not execution.

## 5. The verified order

`E0` carries a linear order generated from the syntactic comparator.

The central theorem is:

```lean
E0.lt_iff_eval_lt (a b : E0) :
  a < b ↔ E0.eval a < E0.eval b
```

The non-strict version is:

```lean
E0.le_iff_eval_le
```

Consequences include:

```lean
E0.eval_injective
E0.eval_strictMono
E0.eval_monotone
E0.evalOrderEmbedding : E0 ↪o Ordinal
E0.eval_lt_eval_iff
E0.eval_le_eval_iff
```

Typical use:

```lean
example (a b : E0) :
    a < b ↔ E0.eval a < E0.eval b :=
  E0.lt_iff_eval_lt a b
```

## 6. Interoperability with mathlib `ONote` and `NONote`

At the raw level:

```lean
E0Term.toONote   : E0Term → ONote
E0Term.ofONote   : ONote → E0Term
E0Term.equivONote : E0Term ≃ ONote
```

The raw bridge preserves semantics and comparison:

```lean
E0Term.repr_toONote
E0Term.eval_ofONote
E0Term.cmp_toONote
```

Normality agrees exactly:

```lean
E0Term.isNormal_iff_nf_toONote
```

At the canonical level:

```lean
E0.toNONote    : E0 → NONote
E0.ofNONote    : NONote → E0
E0.equivNONote : E0 ≃ NONote
```

and the ordered systems are isomorphic:

```lean
E0.orderIsoNONote : E0 ≃o NONote
```

The bridge is useful for interoperability and for reusing mathlib's mature ε₀ algorithms. It is not the definition of this project's raw comparator.

## 7. Notation-level ordinal operations

The following instances are available on `E0`:

```lean
Zero E0
One E0
Add E0
Sub E0
Mul E0
Pow E0 E0
```

Thus:

```lean
a + b
a - b
a * b
a ^ b
```

denote ordinal addition, ordinal subtraction, ordinal multiplication, and ordinal exponentiation on canonical ε₀ notations.

The operations are transported through `NONote`, and the conversion commutes with them:

```lean
E0.toNONote_add
E0.toNONote_sub
E0.toNONote_mul
E0.toNONote_pow
```

Their semantic correctness theorems are simp lemmas:

```lean
E0.eval_add
E0.eval_sub
E0.eval_mul
E0.eval_pow
```

For example:

```lean
example (a b : E0) :
    E0.eval (a * b) = E0.eval a * E0.eval b := by
  simp

example (a b : E0) :
    E0.eval (a ^ b) = E0.eval a ^ E0.eval b := by
  simp
```

## 8. Exact completeness below ε₀

Every canonical notation evaluates below ε₀:

```lean
E0.eval_lt_epsilon_zero (a : E0) :
  E0.eval a < ε₀
```

Every ordinal below ε₀ has a canonical representative:

```lean
E0.exists_eval_eq_of_lt_epsilon_zero
    {α : Ordinal} (h : α < ε₀) :
    ∃ a : E0, E0.eval a = α
```

The exact range theorem is:

```lean
E0.range_eval_eq_Iio_epsilon_zero :
  Set.range E0.eval = Set.Iio ε₀
```

Equivalently:

```lean
E0.mem_range_eval_iff :
  α ∈ Set.range E0.eval ↔ α < ε₀
```

Together with the order embedding, this is the core ε₀ order-type certification. In v0.3.0 it is also recovered through `E0.notationSystem` and the generic exact-initial-segment API.

## 9. Fundamental-sequence classification

The executable classifier is:

```lean
E0.fundamentalSequence :
  E0 → E0.FundamentalSequenceResult
```

with result type:

```lean
inductive E0.FundamentalSequenceResult
  | zero
  | succ (predecessor : E0)
  | limit (seq : Nat → E0)
```

The master correctness theorem is:

```lean
E0.fundamentalSequence_has_prop
```

Its semantic specification says:

- `zero` means the input evaluates to ordinal zero;
- `succ predecessor` means the input evaluates to the ordinal successor of the returned predecessor;
- `limit seq` means the input evaluates to a genuine limit ordinal, `seq` is strictly increasing and bounded by the input notation, and its semantic values are cofinal below the represented ordinal.

The branch-specific convenience API includes:

```lean
E0.fundamentalSequence_eq_zero_eval
E0.eq_zero_of_fundamentalSequence_eq_zero

E0.fundamentalSequence_eq_succ_eval
E0.fundamentalSequence_predecessor_lt

E0.fundamentalSequence_eq_limit_isSuccLimit
E0.fundamentalSequence_eq_limit_step_lt
E0.fundamentalSequence_eq_limit_strictMono
E0.fundamentalSequence_eq_limit_lt
E0.fundamentalSequence_eq_limit_cofinal
```

## 10. Convergence of limit fundamental sequences

For a limit branch, semantic cofinality is packaged as an indexed-supremum theorem:

```lean
E0.fundamentalSequence_eq_limit_iSup_eval
    (h : E0.fundamentalSequence a = .limit seq) :
    (⨆ i, E0.eval (seq i)) = E0.eval a
```

Thus the verified fundamental sequence does not merely stay below the represented ordinal: its semantic values converge to it exactly.

## 11. Ergonomic limit API

When a proof already knows that `E0.eval a` is a limit ordinal, callers need not carry a classifier equality.

The certified bundle is:

```lean
E0.LimitFundamentalSequenceData (a : E0)
```

It contains:

```lean
seq        : Nat → E0
strictMono : StrictMono seq
lt         : ∀ i, seq i < a
cofinal    : ∀ {α : Ordinal}, α < E0.eval a → ∃ i, α < E0.eval (seq i)
iSup_eval  : (⨆ i, E0.eval (seq i)) = E0.eval a
```

The direct accessor is:

```lean
E0.limitFundamentalSequence
    (a : E0) (hlim : Order.IsSuccLimit (E0.eval a)) :
    Nat → E0
```

and its projection theorems are:

```lean
E0.limitFundamentalSequence_strictMono
E0.limitFundamentalSequence_lt
E0.limitFundamentalSequence_cofinal
E0.limitFundamentalSequence_iSup_eval
```

Typical use:

```lean
example (a : E0) (hlim : Order.IsSuccLimit (E0.eval a)) :
    (⨆ i, E0.eval (E0.limitFundamentalSequence a hlim i)) = E0.eval a :=
  E0.limitFundamentalSequence_iSup_eval a hlim
```

## 12. Module map

The implementation is split into small proof layers:

- `Term.lean`: raw syntax and structural utilities.
- `Compare.lean`: executable raw comparison.
- `NormalForm.lean`: canonicality and `E0`.
- `Semantics.lean`: interpretation into `Ordinal`.
- `SemanticBounds.lean` and `SemanticCompare.lean`: local ordinal estimates.
- `Correctness.lean`: comparison soundness and completeness.
- `LinearOrder.lean`: the canonical linear order.
- `OrderEmbedding.lean`: semantic order embedding.
- `MathlibBridge.lean`: raw `ONote` bridge.
- `CanonicalBridge.lean`: canonical `NONote` bridge.
- `MathlibOrderIso.lean`: `E0 ≃o NONote`.
- `Operations.lean`: notation-level arithmetic.
- `Completeness.lean`: exact semantic range below ε₀.
- `FundamentalSequence.lean`: executable classifier and certified transport from mathlib `ONote`.
- `FundamentalSequenceAPI.lean`: branch-specific zero/successor/limit theorems.
- `FundamentalSequenceConvergence.lean`: indexed-supremum convergence theorem.
- `LimitFundamentalSequence.lean`: ergonomic certified limit-sequence API.

v0.3.0 additionally packages this development as `E0.notationSystem : OrdinalNotationSystem E0` and `E0.classifier : OrdinalClassifier E0.notationSystem`. See [`generic-api.md`](generic-api.md) and `OrdinalAnalysis/Examples/Epsilon0Generic.lean` for the reusable interface and compiled examples.

Import `OrdinalAnalysis` unless a narrower dependency is useful.

## 13. Computational boundary

The intended pattern is:

```text
finite syntax
    ↓ executable checking/comparison
canonical E0
    ↓ certified semantics
Ordinal
```

Use `E0Term`, `E0`, and their executable operations for computation. Use `eval`, order-reflection theorems, and completeness when proving that those computations have the intended ordinal meaning.
