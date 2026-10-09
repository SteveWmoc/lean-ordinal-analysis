# lean-ordinal-analysis

[![Build](https://github.com/SteveWmoc/lean-ordinal-analysis/actions/workflows/build.yml/badge.svg)](https://github.com/SteveWmoc/lean-ordinal-analysis/actions/workflows/build.yml)

Executable recursive ordinal notation systems in Lean 4, with verified semantics and order types.

Version 0.1.0 is the ε₀ milestone: the project defines a finite, computable notation system and proves that its canonical terms represent exactly the ordinals below ε₀.

## What v0.1.0 provides

The ε₀ development includes:

- a recursive raw syntax `E0Term` for Cantor normal form;
- an executable normal-form predicate;
- an executable syntactic comparator independent of abstract ordinal comparison;
- the canonical subtype `E0`;
- a verified linear order on `E0`;
- a semantic interpretation `E0.eval : E0 → Ordinal`;
- soundness and completeness of syntactic comparison;
- an order embedding `E0 ↪o Ordinal`;
- a structural bridge `E0Term ≃ ONote`;
- a canonical order isomorphism `E0 ≃o NONote`;
- notation-level ordinal addition, subtraction, multiplication, and exponentiation;
- semantic correctness theorems for those operations;
- the exact range theorem
  ```lean
  E0.range_eval_eq_Iio_epsilon_zero :
    Set.range E0.eval = Set.Iio ε₀
  ```

The last theorem identifies the represented order type exactly with the initial segment below ε₀.

## Design

The project keeps three layers separate:

1. **Finite syntax.** Recursive terms on which Lean can compute.
2. **Canonical notation.** Normal forms with executable comparison.
3. **Semantic ordinal.** Interpretation into mathlib's `Ordinal`, used to certify the syntax rather than define it.

This separation is intentional. The raw comparator does not call abstract ordinal comparison. The current ε₀ implementation does reuse mathlib's `ONote`/`NONote` machinery for canonical interoperability and arithmetic after the independent syntax and comparison theory has been verified.

See [`docs/design.md`](docs/design.md) for the frozen initial design and [`docs/api.md`](docs/api.md) for the user-facing API guide.

## Toolchain

v0.1.0 is pinned to:

- Lean `v4.34.1`
- mathlib `v4.34.1`

The package version in `lakefile.toml` is `0.1.0`.

## Build

With `elan` installed:

```bash
git clone https://github.com/SteveWmoc/lean-ordinal-analysis.git
cd lean-ordinal-analysis
lake exe cache get
lake build
```

The root module is:

```lean
import OrdinalAnalysis
```

## Quick API sketch

```lean
import OrdinalAnalysis

open OrdinalAnalysis

#eval E0Term.compareRaw E0Term.zero E0Term.one

example (a b : E0) :
    a < b ↔ E0.eval a < E0.eval b :=
  E0.lt_iff_eval_lt a b

example (a b : E0) :
    E0.eval (a + b) = E0.eval a + E0.eval b := by
  simp

#check E0.orderIsoNONote
#check E0.range_eval_eq_Iio_epsilon_zero
```

`E0.eval` is noncomputable because mathlib ordinal arithmetic is noncomputable. The notation syntax, normality checker, comparator, and transported notation algorithms remain finite computational objects.

## Roadmap

### v0.1 - ε₀

Complete. The canonical notation type has verified order type exactly ε₀, with executable comparison and notation-level arithmetic.

### v0.2 - fundamental sequences

Planned next:

- zero/successor/limit classification;
- fundamental sequences for limit notations;
- monotonicity and boundedness;
- semantic cofinality/convergence.

### v0.3 - generic notation-system API

Extract reusable abstractions after the ε₀ implementation has exposed the right interface.

### v0.4 - Γ₀

Develop finite Veblen normal forms, executable comparison, interpretation through mathlib's Veblen hierarchy, and an exact Γ₀ order-type theorem.

Longer-term work may move beyond mathlib's existing concrete notation systems toward collapsing-function and Bachmann-Howard style notations.

## Scope

v0.1.0 does not formalize Gentzen's consistency proof, infinitary proof systems, cut elimination, fast-growing hierarchies, or collapsing-function systems. Its purpose is the notation infrastructure itself.

## Citation and archival metadata

Citation metadata is provided in [`CITATION.cff`](CITATION.cff). Zenodo-specific release metadata is provided in [`.zenodo.json`](.zenodo.json).

The v0.1.0 release procedure, including the post-release DOI update, is documented in [`docs/release-v0.1.0.md`](docs/release-v0.1.0.md). The DOI is intentionally not hard-coded before Zenodo assigns it.

See [`CHANGELOG.md`](CHANGELOG.md) for the release summary.

## License

This project is released under the [MIT License](LICENSE).
