# Initial Γ₀ design: finite Veblen normal forms

This document freezes the first concrete design for the v0.4 Γ₀ milestone.
As with ε₀, the goal is to build a finite executable notation system first and
use mathlib ordinals only as a semantic certification layer.

The target endpoint is a canonical notation type whose verified order type is
exactly the Feferman-Schütte ordinal Γ₀.

## 1. Design invariant

The project retains the same three-layer separation used successfully for ε₀:

1. **Raw syntax:** finite recursive data and executable algorithms.
2. **Canonical notation:** raw terms satisfying a decidable normal-form
   condition and carrying an executable linear order.
3. **Semantic ordinal:** interpretation into mathlib `Ordinal`, used to prove
   the concrete syntax and algorithms correct.

The executable comparator must not be implemented by evaluating terms into
abstract ordinals and comparing there.

Once the concrete system is certified, it should instantiate the generic
v0.3 interfaces `OrdinalNotationSystem` and, when fundamental sequences are
available, `OrdinalClassifier`.

## 2. Raw term representation

The initial datatype is:

```lean
inductive G0Term where
  | zero
  | veblen
      (index : G0Term)
      (arg : G0Term)
      (coeff : Nat)
      (tail : G0Term)
```

A node

```lean
G0Term.veblen index arg coeff tail
```

is intended to represent

```text
φ_index(arg) * (coeff + 1) + tail.
```

Semantically, `φ_α(β)` will be interpreted by
`Ordinal.veblen (eval α) (eval β)`.

The stored natural coefficient is again the predecessor of the mathematical
positive coefficient. This mirrors `E0Term` and permits compact representation
of repeated equal principal terms.

The raw datatype intentionally admits malformed and noncanonical expressions.

## 3. Why finite sums of Veblen principal terms?

Mathlib proves that for every ordinal exponent `x` there is a unique
Veblen decomposition of the principal ordinal `ω^x`:

```text
ω^x = φ_{invVeblen₁ x}(invVeblen₂ x),
```

with the second component strictly below `ω^x`.

Mathlib's own documentation notes that combining this inverse-Veblen
decomposition with Cantor normal form yields predicative ordinal notation up to
Γ₀.

This suggests exactly the representation above:

- ordinary CNF supplies a finite sum of additive principal terms;
- inverse Veblen replaces each `ω^x` by a canonical `φ_α(β)`;
- coefficients aggregate repeated equal principal terms;
- the index, argument, and tail are recursively represented by the same syntax.

This is also close enough to the ε₀ representation that existing proof
architecture can be reused without forcing Γ₀ into Cantor-normal-form syntax.

## 4. Intended semantic interpretation

After the computational layers are in place, define:

```lean
eval : G0Term → Ordinal
```

by

```text
eval zero = 0

eval (veblen index arg coeff tail)
  = Ordinal.veblen (eval index) (eval arg) * (coeff + 1)
      + eval tail.
```

The semantic target for canonical terms is the initial segment below
`Ordinal.Γ₀`.

## 5. Canonical Veblen normal form

The intended normal-form predicate will recursively require the index,
argument, and tail to be normal.

For each leading principal term `φ_α(β)`, canonicality must additionally
enforce the inverse-Veblen side condition

```text
β < φ_α(β).
```

This condition rules out noncanonical presentations in which the argument is
already a fixed point of the chosen Veblen function. It is the syntactic
counterpart of the uniqueness condition used by mathlib's
`invVeblen₁`/`invVeblen₂` decomposition.

For a nonzero tail, its leading Veblen principal term must be strictly smaller
than the current leading principal term. Thus a canonical term is a finite
descending sum of canonical Veblen principal terms.

The exact executable formulation will be frozen only after the raw principal
comparison has been implemented.

## 6. Executable principal comparison

Mathlib proves the semantic comparison law

```text
φ_{α₁}(β₁) < φ_{α₂}(β₂)
```

iff one of:

1. `α₁ = α₂` and `β₁ < β₂`;
2. `α₁ < α₂` and `β₁ < φ_{α₂}(β₂)`;
3. `α₂ < α₁` and `φ_{α₁}(β₁) < β₂`.

This recursive shape will guide the finite syntactic principal comparator.

A natural termination measure is based on structural node count: in the
second and third cases one side is replaced by a proper recursive argument,
so an appropriate sum of node counts decreases.

Once principal terms compare, full normal forms compare lexicographically by:

1. leading Veblen principal term;
2. positive coefficient;
3. tail.

The semantic theorem from mathlib is a proof target for this algorithm, not
its implementation.

## 7. Distinguished raw terms

The initial syntax provides convenient raw representatives:

```text
1   = φ₀(0)
ω   = φ₀(1)
ε₀  = φ₁(0)
```

These are structural conveniences only. Their semantic correctness will be
proved after `eval` is introduced.

## 8. Γ₀ bound and completeness strategy

Mathlib defines Γ₀ as the least fixed point of `α ↦ φ_α(0)` and provides:

```lean
Ordinal.lt_gamma_zero
Ordinal.iterate_veblen_lt_gamma_zero
```

For completeness, the expected route is:

1. decompose an arbitrary ordinal below Γ₀ by finite CNF;
2. use `invVeblen₁` and `invVeblen₂` to decompose each principal
   `ω^x`;
3. recursively represent the Veblen index and argument;
4. prove the resulting finite syntax is canonical;
5. show its evaluation is the original ordinal.

For the upper bound, canonical terms should be shown to lie below a finite
iteration of `α ↦ φ_α(0)`, then below Γ₀.

The proof details are deliberately deferred until comparison and normality are
stable.

## 9. Relationship to the generic v0.3 API

The Γ₀ implementation is the first serious second client of the generic layer.

The intended endpoint is:

```lean
G0.notationSystem : OrdinalNotationSystem G0
```

with bound `Ordinal.Γ₀`.

This project should adapt the generic interface only if Γ₀ reveals a genuine
missing abstraction. It should not distort the concrete Γ₀ syntax merely to
fit the generic layer.

## 10. Out of scope for the first slices

The initial Γ₀ slices do not include:

- fundamental sequences;
- a generic Veblen notation framework;
- Bachmann-Howard or collapsing functions;
- infinitary proof systems;
- cut elimination;
- autonomous progressions or predicative-analysis metatheory.

The immediate sequence is:

1. raw `G0Term` syntax and structural utilities;
2. executable raw Veblen-principal comparison;
3. Veblen normality and canonical `G0`;
4. executable order on canonical terms;
5. semantic interpretation into `Ordinal.veblen`;
6. comparison correctness and order embedding;
7. exact semantic range below Γ₀;
8. instantiate `OrdinalNotationSystem`;
9. only then design Γ₀ fundamental sequences.
