# Changelog

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
