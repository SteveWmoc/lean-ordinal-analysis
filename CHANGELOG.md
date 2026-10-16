# Changelog

## 0.3.0

Generic verified ordinal-notation API milestone.

### Added

- `OrdinalNotationSystem N`, a reusable interface for canonical ordinal notation systems with:
  - semantic evaluation;
  - an exact ordinal bound;
  - order correctness;
  - completeness below the bound.
- Generic monotonicity, injectivity, and semantic order-embedding theorems.
- Generic exact-range theorem
  ```lean
  system.range_eval_eq_Iio :
    Set.range system.eval = Set.Iio system.bound
  ```
- Generic exact order isomorphism
  ```lean
  system.orderIsoIio :
    N ≃o Set.Iio system.bound
  ```
- Generic `ClassificationResult N` with zero, successor, and limit branches.
- `OrdinalClassifier system`, bundling a classifier with its semantic correctness proof.
- Generic successor-predecessor and limit-sequence consequences.
- Generic strict monotonicity, boundedness, semantic cofinality, and indexed-supremum convergence for limit sequences.
- `OrdinalClassifier.LimitSequenceData` and the ergonomic `classifier.limitSequence` API.
- `E0.notationSystem : OrdinalNotationSystem E0`.
- `E0.classifier : OrdinalClassifier E0.notationSystem`.
- `E0.orderIsoIioEpsilonZero : E0 ≃o Set.Iio ε₀`.
- Compiled ε₀ examples exercising the complete generic API.
- Dedicated generic API guide and v0.3.0 release documentation.

### Design

The generic interface deliberately begins at canonical notation types. It does not prescribe raw syntax, normal forms, normalization, arithmetic, a distinguished syntactic zero, or a concrete comparison algorithm. Γ₀/Veblen notation is reserved for v0.4 as the first serious second implementation of the abstraction.

### Toolchain

- Lean `v4.34.1`.
- mathlib `v4.34.1`.

### License

- Released under the MIT License.

## 0.2.0

Fundamental-sequence milestone for the verified ε₀ notation system.

### Added

- Executable zero/successor/limit classification on canonical `E0` notations.
- Canonical predecessor output for successor notations.
- Canonical fundamental sequences for limit notations.
- Semantic certification of each classifier branch.
- Branch-specific convenience theorems for zero, successor, and limit outputs.
- Strict monotonicity of limit fundamental sequences.
- Proof that every sequence entry lies below the input notation.
- Semantic cofinality below the represented limit ordinal.
- Exact convergence theorem
  ```lean
  E0.fundamentalSequence_eq_limit_iSup_eval
      (h : E0.fundamentalSequence a = .limit seq) :
    (⨆ i, E0.eval (seq i)) = E0.eval a
  ```
  for a limit-classifier result.
- `E0.LimitFundamentalSequenceData`, a certified limit-sequence bundle.
- Ergonomic `E0.limitFundamentalSequence` API and direct monotonicity, boundedness, cofinality, and convergence theorems.
- Updated API guide, README, citation metadata, Zenodo metadata, and release procedure.

### Toolchain

- Lean `v4.34.1`.
- mathlib `v4.34.1`.

### Scope

v0.2.0 completes the fundamental-sequence layer. Generic notation-system abstractions, Γ₀/Veblen notation, Gentzen-style proof systems, fast-growing hierarchies, and collapsing functions remain outside this release.

### License

- Released under the MIT License.

## 0.1.0

First public ε₀ milestone.

### Added

- Recursive raw Cantor-normal-form syntax `E0Term`.
- Executable normal-form checking and canonical subtype `E0`.
- Executable syntactic comparison on raw terms.
- Verified linear order on canonical terms.
- Semantic interpretation into mathlib `Ordinal`.
- Soundness and completeness of syntactic strict comparison.
- Injective semantic map and order embedding into `Ordinal`.
- Raw equivalence with mathlib `ONote`.
- Canonical equivalence and order isomorphism with mathlib `NONote`.
- Notation-level ordinal addition, subtraction, multiplication, and exponentiation.
- Semantic correctness theorems for notation-level arithmetic.
- Upper-bound theorem `E0.eval_lt_epsilon_zero`.
- Completeness theorem `E0.exists_eval_eq_of_lt_epsilon_zero`.
- Exact range theorem
  ```lean
  E0.range_eval_eq_Iio_epsilon_zero :
    Set.range E0.eval = Set.Iio ε₀
  ```
- User-facing API guide and release documentation.
- GitHub citation metadata and Zenodo release metadata.

### Toolchain

- Lean `v4.34.1`.
- mathlib `v4.34.1`.

### Scope

Fundamental sequences are deliberately not part of v0.1.0. They begin the next development milestone.

### License

- Released under the MIT License.
