# Initial design: ordinal notations below ε₀

This document freezes the first implementation target for `lean-ordinal-analysis`.
The purpose of the first phase is not to formalize Gentzen's consistency proof.
It is to build and verify a concrete recursive notation system whose order type
is exactly ε₀.

## 1. Separation of layers

The ε₀ implementation has three distinct layers.

1. **Raw syntax.** Finite recursive terms on which Lean can compute.
2. **Canonical notation.** Raw terms satisfying a Cantor-normal-form predicate.
3. **Semantics.** An interpretation of raw terms into mathlib's abstract
   `Ordinal`.

The first two layers define the notation system.  The semantic layer certifies
it.  In particular, executable comparison and normalization must not be
implemented by converting terms to `Ordinal` and comparing there.

This separation is a project invariant.

## 2. Raw term representation

The initial datatype will be equivalent to

```lean
inductive E0Term
  | zero
  | cnf (exp : E0Term) (coeff : Nat) (tail : E0Term)
```

The constructor

```
cnf exp coeff tail
```

represents

```
ω ^ exp * (coeff + 1) + tail.
```

Thus the stored natural number is the predecessor of the mathematical
coefficient.  Every nonzero summand therefore has a positive coefficient
without carrying a positivity proof in the datatype.

The raw datatype deliberately admits noncanonical expressions.  Canonicality
will not be built into recursive constructor fields.

## 3. Canonical form

A predicate

```lean
IsNormal : E0Term → Prop
```

will express Cantor normal form.

Conceptually:

- `zero` is normal;
- `cnf exp coeff tail` is normal when
  - `exp` is normal;
  - `tail` is normal; and
  - either `tail = zero`, or the leading exponent of `tail` is strictly
    smaller than `exp`.

The canonical notation type will initially be a subtype:

```lean
abbrev E0 := { t : E0Term // IsNormal t }
```

We may later replace the abbreviation by a thin structure if ergonomics
require it, but the mathematical representation is fixed: recursive raw syntax
plus a separate normal-form invariant.

A helper such as

```lean
leadingExponent? : E0Term → Option E0Term
```

may be used to state or decide normality.

## 4. Syntactic order

Comparison is defined recursively on syntax.

For two nonzero normal forms

```
ω^α * m + β
ω^γ * n + δ
```

comparison is lexicographic:

1. compare `α` and `γ`;
2. if equal, compare the positive coefficients `m` and `n`;
3. if those are equal, compare the tails `β` and `δ`.

Zero is below every nonzero term.

The implementation should expose an executable comparison function and derive
a decidable linear order on `E0`.  Its termination argument must depend only
on the finite term structure.

## 5. Semantic interpretation

After the computational order exists, define

```lean
eval : E0Term → Ordinal
```

by

```
eval zero = 0
eval (cnf exp coeff tail) =
  ω ^ eval exp * (coeff + 1) + eval tail.
```

Here `ω`, exponentiation, multiplication, and addition are ordinal
operations.

The central correctness theorem is, for canonical terms,

```
s < t ↔ eval s < eval t.
```

Consequences should include:

- equality reflection on canonical terms;
- injectivity of `eval : E0 → Ordinal`;
- an order embedding `E0 ↪o Ordinal`.

The semantic map is a proof device and interoperability layer; it is not the
definition of the executable order.

## 6. The ε₀ completeness target

The v0.1 endpoint is the pair of bounds

```
∀ t : E0, eval t < ε₀
```

and

```
∀ α : Ordinal, α < ε₀ → ∃ t : E0, eval t = α.
```

Together with order reflection, these establish that the concrete recursive
notation system has order type exactly ε₀.

We will use mathlib's existing abstract ordinal development as an independent
semantic target.

## 7. Operations

Only after comparison and semantics are verified will the project add
notation-level operations.  The initial candidates are:

- successor;
- ordinal addition;
- multiplication by a natural coefficient;
- `α ↦ ω^α`;
- normalization of suitable raw expressions.

Each computational operation should come with a theorem that `eval`
commutes with it.

## 8. Fundamental sequences

Fundamental sequences are deferred to v0.2.  For each limit notation `λ`,
the intended API should eventually provide terms `λ[n]` and prove the
expected syntactic and semantic facts, including monotonicity, boundedness,
and convergence to `eval λ`.

They are deliberately not part of the first datatype design.

## 9. Generic abstraction

There will be no `OrdinalNotationSystem` typeclass in the initial phase.
The reusable abstraction will be extracted only after the ε₀ implementation
has revealed which interface is actually useful.

The Γ₀ implementation will then serve as the first serious test of that
abstraction.

## 10. Out of scope for v0.1

The following are explicitly outside the first milestone:

- Gentzen's consistency proof for PA;
- infinitary proof calculi;
- cut elimination;
- fast-growing or Hardy hierarchies;
- Goodstein and hydra applications;
- primitive-recursive Gödel coding of the notation syntax;
- Bachmann–Howard or other collapsing-function systems;
- the full generic notation-system API;
- Γ₀ itself.

These are possible later layers, not prerequisites for validating the ε₀
notation system.

## 11. Planned implementation slices

The intended order of development is:

1. raw `E0Term` syntax and structural utilities;
2. `IsNormal` and decidability;
3. recursive comparison and the order on `E0`;
4. semantic evaluation into `Ordinal`;
5. comparison correctness and order embedding;
6. notation-level operations and normalization;
7. completeness below ε₀.

A slice should remain small enough that failures in representation, recursion,
or theorem statements are caught before later layers depend on them.
