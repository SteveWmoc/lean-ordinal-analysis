# lean-ordinal-analysis

[![Build](https://github.com/SteveWmoc/lean-ordinal-analysis/actions/workflows/build.yml/badge.svg)](https://github.com/SteveWmoc/lean-ordinal-analysis/actions/workflows/build.yml)
[![DOI](https://zenodo.org/badge/1376449795.svg)](https://doi.org/10.5281/zenodo.23272263)

Executable recursive ordinal notation systems in Lean 4, with verified semantics and order types.

Version 0.3.0 extracts a reusable verified ordinal-notation API from the completed ε₀ development, including exact initial-segment theory, certified zero/successor/limit classifiers, and generic limit-sequence convergence.

## What v0.3.0 provides

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
- executable zero/successor/limit classification via `E0.fundamentalSequence`;
- certified successor predecessors and limit fundamental sequences;
- strict monotonicity and boundedness of limit sequences;
- semantic cofinality below the represented limit ordinal;
- convergence of semantic values:
  ```lean
  E0.fundamentalSequence_eq_limit_iSup_eval
      (h : E0.fundamentalSequence a = .limit seq) :
    (⨆ i, E0.eval (seq i)) = E0.eval a
  ```
- an ergonomic limit-only API through `E0.limitFundamentalSequence`;
- the generic `OrdinalNotationSystem` interface;
- generic exact-range and order-isomorphism theory;
- the generic `ClassificationResult` and certified `OrdinalClassifier` interfaces;
- generic successor/limit consequences, cofinality, and convergence;
- the generic ergonomic `OrdinalClassifier.limitSequence` API;
- `E0.notationSystem` and `E0.classifier` as reference implementations;
- compiled examples showing the ε₀ system satisfies the complete generic API.

The range theorem `E0.range_eval_eq_Iio_epsilon_zero` identifies the represented order type exactly with the initial segment below ε₀.

## Current Γ₀ development

The development branch now includes finite Veblen syntax, an executable
normal-form checker and comparator, semantic comparison correctness, and
uniqueness of canonical normal forms. Canonical `G0` notations carry a verified
linear order and an ordinal order embedding:

```lean
G0.evalOrderEmbedding : G0 ↪o Ordinal
G0.eval_lt_eval_iff (a b : G0) : G0.eval a < G0.eval b ↔ a < b
G0.eval_le_eval_iff (a b : G0) : G0.eval a ≤ G0.eval b ↔ a ≤ b
```

Strict comparison remains the raw syntactic relation. The linear order's
decision procedures are obtained from `G0Term.compareRaw`; ordinal evaluation
certifies their correctness. Compiled examples are in
[`OrdinalAnalysis/Examples/Gamma0Order.lean`](OrdinalAnalysis/Examples/Gamma0Order.lean).

The exact Γ₀ range and order-type theorem remain future work.

## Design

The project keeps three layers separate:

1. **Finite syntax.** Recursive terms on which Lean can compute.
2. **Canonical notation.** Normal forms with executable comparison.
3. **Semantic ordinal.** Interpretation into mathlib's `Ordinal`, used to certify the syntax rather than define it.

This separation is intentional. The raw comparator does not call abstract ordinal comparison. The current ε₀ implementation does reuse mathlib's `ONote`/`NONote` machinery for canonical interoperability and arithmetic after the independent syntax and comparison theory has been verified.

See [`docs/design.md`](docs/design.md) for the frozen initial ε₀ design, [`docs/api.md`](docs/api.md) for the detailed ε₀ API, and [`docs/generic-api.md`](docs/generic-api.md) for the v0.3 generic notation-system guide.

## Toolchain

v0.3.0 is pinned to:

- Lean `v4.34.1`
- mathlib `v4.34.1`

The package version in `lakefile.toml` is `0.3.0`.

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
#check E0.fundamentalSequence
#check E0.limitFundamentalSequence
#check E0.limitFundamentalSequence_iSup_eval
#check E0.notationSystem
#check E0.notationSystem.orderIsoIio
#check E0.classifier
#check E0.classifier.limitSequence_iSup_eval
```

`E0.eval` is noncomputable because mathlib ordinal arithmetic is noncomputable. The notation syntax, normality checker, comparator, and transported notation algorithms remain finite computational objects.

## Roadmap

### v0.1 - ε₀

Complete. The canonical notation type has verified order type exactly ε₀, with executable comparison and notation-level arithmetic.

### v0.2 - fundamental sequences

Complete. The ε₀ notation system now includes:

- executable zero/successor/limit classification;
- canonical predecessor output in the successor branch;
- canonical fundamental sequences in the limit branch;
- strict monotonicity and boundedness;
- semantic cofinality;
- the supremum/convergence theorem
  ```lean
  E0.fundamentalSequence_eq_limit_iSup_eval
      (h : E0.fundamentalSequence a = .limit seq) :
    (⨆ i, E0.eval (seq i)) = E0.eval a
  ```
- an ergonomic limit API that hides classifier equalities once a semantic limit hypothesis is available.

### v0.3 - generic notation-system API

Complete. The project now provides:

- `OrdinalNotationSystem` for exact canonical notation systems;
- generic order embedding and exact initial-segment theory;
- `ClassificationResult` and certified `OrdinalClassifier`;
- generic zero/successor/limit consequences;
- generic cofinality and indexed-supremum convergence;
- an ergonomic generic limit-sequence API;
- ε₀ adapters and compiled examples demonstrating the abstraction.

### v0.4 - Γ₀

Develop finite Veblen normal forms, executable comparison, interpretation through mathlib's Veblen hierarchy, and an exact Γ₀ order-type theorem.

Longer-term work may move beyond mathlib's existing concrete notation systems toward collapsing-function and Bachmann-Howard style notations.

## Scope

v0.3.0 does not yet add Γ₀/Veblen syntax, Gentzen's consistency proof, infinitary proof systems, cut elimination, fast-growing hierarchies, or collapsing-function systems. Its purpose is the reusable verified notation-system infrastructure on which later concrete systems can build.

## Citation and archival metadata

Citation metadata is provided in [`CITATION.cff`](CITATION.cff). Zenodo-specific release metadata is provided in [`.zenodo.json`](.zenodo.json).

Release procedures are documented in [`docs/release-v0.1.0.md`](docs/release-v0.1.0.md), [`docs/release-v0.2.0.md`](docs/release-v0.2.0.md), and [`docs/release-v0.3.0.md`](docs/release-v0.3.0.md). The archived project is available through the Zenodo DOI badge above.

See [`CHANGELOG.md`](CHANGELOG.md) for the release summary.

## License

This project is released under the [MIT License](LICENSE).
