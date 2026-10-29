# Generic notation-system API

Version 0.3.0 extracts the reusable semantic interface revealed by the ε₀ development.

The generic layer begins at a **canonical notation type**. It deliberately does not prescribe raw syntax, normal forms, normalization algorithms, arithmetic operations, or a concrete comparison implementation. Those details belong to each notation system.

The simplest import is:

```lean
import OrdinalAnalysis
open OrdinalAnalysis
```

## 1. Core notation systems

A verified notation system is packaged as:

```lean
structure OrdinalNotationSystem (N : Type u) [LinearOrder N] where
  eval : N → Ordinal
  bound : Ordinal
  eval_lt_bound : ∀ a, eval a < bound
  lt_iff_eval_lt : ∀ a b, a < b ↔ eval a < eval b
  complete : ∀ {α}, α < bound → ∃ a, eval a = α
```

The fields say that the notation order is exactly semantic ordinal order and that the semantic range covers every ordinal below `bound`.

From those fields the library derives:

```lean
system.eval_strictMono
system.eval_monotone
system.eval_injective
system.evalOrderEmbedding
system.eval_lt_eval_iff
system.le_iff_eval_le
system.eval_le_eval_iff
```

## 2. Exact initial segments

Every `OrdinalNotationSystem` automatically satisfies:

```lean
system.mem_range_eval_iff
system.range_eval_eq_Iio
```

and has a canonical order isomorphism

```lean
system.orderIsoIio :
  N ≃o Set.Iio system.bound
```

Thus the generic interface certifies the exact order type of the canonical notation system.

For ε₀:

```lean
E0.notationSystem : OrdinalNotationSystem E0

E0.orderIsoIioEpsilonZero :
  E0 ≃o Set.Iio ε₀
```

The Γ₀ implementation also satisfies this core interface:

```lean
G0.notationSystem : OrdinalNotationSystem G0

G0.orderIsoIioGammaZero :
  G0 ≃o Set.Iio Γ₀
```

`G0.notationSystem.eval` is the existing `G0.eval` and its bound is Γ₀.
The isomorphism's forward map agrees with `G0.evalOrderEmbeddingIio`;
its inverse agrees with `G0.ofOrdinal`. The adapter uses the existing
order-correctness, soundness, and completeness theorems without modifying
the generic interface.

Compiled examples in `OrdinalAnalysis/Examples/Gamma0Generic.lean` exercise
the generic range and order theorems, the order isomorphism, and its compatibility
with the concrete maps. This core adapter does not supply a Γ₀ classifier;
the classifier interface described below remains a separate contract.

## 3. Generic classification

The generic classifier result is:

```lean
inductive ClassificationResult (N : Type u)
  | zero
  | succ (predecessor : N)
  | limit (seq : Nat → N)
```

Its semantic specification is:

```lean
ClassificationResult.Satisfies
```

relative to an `OrdinalNotationSystem`.

A certified classifier is:

```lean
OrdinalClassifier system
```

with:

```lean
classifier.classify : N → ClassificationResult N
classifier.classify_satisfies
```

The limit branch requires the returned sequence to be stepwise increasing, bounded below the input notation, and semantically cofinal.

The existing ε₀ algorithm is packaged as:

```lean
E0.classifier : OrdinalClassifier E0.notationSystem
```

without changing the original v0.2 classifier API.

## 4. Generic classifier consequences

For every certified classifier the library derives:

```lean
classifier.classify_eq_zero_eval

classifier.classify_eq_succ_eval
classifier.classify_predecessor_lt

classifier.classify_eq_limit_isSuccLimit
classifier.classify_eq_limit_step_lt
classifier.classify_eq_limit_strictMono
classifier.classify_eq_limit_lt
classifier.classify_eq_limit_cofinal
classifier.classify_eq_limit_iSup_eval
```

In particular, the convergence theorem is generic:

```lean
classifier.classify_eq_limit_iSup_eval
    (h : classifier.classify a = .limit seq) :
    (⨆ i, system.eval (seq i)) = system.eval a
```

No ε₀-specific syntax appears in its proof.

## 5. Ergonomic limit API

Once a caller knows semantically that a notation represents a limit ordinal,

```lean
hlim : Order.IsSuccLimit (system.eval a)
```

the generic layer eliminates the impossible zero and successor classifier branches and returns a certified object:

```lean
OrdinalClassifier.LimitSequenceData classifier a
```

containing:

```lean
seq        : Nat → N
strictMono : StrictMono seq
lt         : ∀ i, seq i < a
cofinal    : ∀ {α}, α < system.eval a → ∃ i, α < system.eval (seq i)
iSup_eval  : (⨆ i, system.eval (seq i)) = system.eval a
```

The direct accessor is:

```lean
classifier.limitSequence a hlim
```

with:

```lean
classifier.limitSequence_strictMono
classifier.limitSequence_lt
classifier.limitSequence_cofinal
classifier.limitSequence_iSup_eval
```

## 6. ε₀ as the reference implementation

The file

```text
OrdinalAnalysis/Examples/Epsilon0Generic.lean
```

contains compiled examples showing that the completed ε₀ development satisfies the generic interfaces. Among other things it checks:

```lean
example :
    Set.range E0.notationSystem.eval = Set.Iio ε₀ := by
  simpa using E0.notationSystem.range_eval_eq_Iio

example :
    E0 ≃o Set.Iio ε₀ :=
  E0.orderIsoIioEpsilonZero
```

and exercises the generic classifier and ergonomic limit sequence API.

These are not replacements for the existing ε₀ theorems. They are machine-checked evidence that the abstraction captures the structure already built in v0.1 and v0.2.

## 7. Design boundary

The generic API intentionally does **not** require:

- a raw syntax type;
- a normal-form predicate;
- a normalization algorithm;
- a distinguished syntactic zero;
- arithmetic operations;
- an `ONote` or `NONote` bridge;
- a particular comparison algorithm.

That restraint is deliberate. Γ₀/Veblen notation now supplies a second concrete implementation of the core notation-system and exact-initial-segment interfaces without changing the generic layer. Classifiers and fundamental sequences remain additional structures, rather than requirements of the core interface.
