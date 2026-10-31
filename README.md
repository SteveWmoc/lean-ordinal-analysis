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

Every raw finite term evaluates below Γ₀, even without normality:

```lean
G0Term.eval_lt_gamma_zero (t : G0Term) : G0Term.eval t < Γ₀
G0.eval_lt_gamma_zero (a : G0) : G0.eval a < Γ₀
G0.evalOrderEmbeddingIio : G0 ↪o Set.Iio Γ₀
```

This proves semantic soundness and restricts the canonical embedding to the
initial segment below Γ₀. The proof uses closure under Veblen application,
finite right multiplication, and addition. Compiled examples, including
noncanonical terms, are in
[`OrdinalAnalysis/Examples/Gamma0Bounds.lean`](OrdinalAnalysis/Examples/Gamma0Bounds.lean).

The semantic completeness proof uses a certified decomposition step.
For every nonzero `o < Γ₀`,
`Gamma0Decomposition.decompose o hne hbound` provides `index`, `arg`,
a stored natural `coeff`, and `tail` satisfying

```lean
Ordinal.veblen d.index d.arg * (d.coeff.succ : Ordinal) + d.tail = o
```

All three recursive ordinal inputs are strictly smaller than `o`, and both
the argument and remainder are smaller than the leading Veblen principal term.
This uses inverse Veblen functions and the leading Cantor coefficient and
remainder. It is a noncomputable semantic construction used by the completeness
proof. Examples include the strict inverse-index bound at ε₀ and its failure
at Γ₀.

Completeness is now proved by well-founded ordinal induction. Each recursive
input in the decomposition has a canonical notation; semantic argument and
tail bounds certify that the assembled node passes the executable checker.
The exact range is:

```lean
G0.range_eval_eq_Iio_gamma_zero :
  Set.range G0.eval = Set.Iio Γ₀
```

`G0.ofOrdinal o hbound` chooses the unique canonical notation for `o < Γ₀`.
The simp lemmas `G0.eval_ofOrdinal` and `G0.ofOrdinal_eval` give both round
trips. Consequently `G0.evalOrderEmbeddingIio` is surjective. Compiled examples
are in
[`OrdinalAnalysis/Examples/Gamma0Completeness.lean`](OrdinalAnalysis/Examples/Gamma0Completeness.lean).

The Γ₀ development now satisfies the same core generic interface as ε₀:

```lean
G0.notationSystem : OrdinalNotationSystem G0
G0.orderIsoIioGammaZero : G0 ≃o Set.Iio Γ₀
```

The order isomorphism is obtained from the existing generic exact-initial-segment
theory. Its forward map agrees with `G0.evalOrderEmbeddingIio`, and its inverse
agrees with `G0.ofOrdinal`. Thus the canonical notation order is exactly the
ordinal initial segment below Γ₀. The generic API needed no changes.

Compiled adapter, order, range, and inverse-compatibility examples are in
[`OrdinalAnalysis/Examples/Gamma0Generic.lean`](OrdinalAnalysis/Examples/Gamma0Generic.lean).
An executable shape classifier now distinguishes zero, successors, and limits:

```lean
G0.successorView : G0 → G0.SuccessorView
G0.predecessor? : G0 → Option G0
```

The successor case returns a canonical predecessor with certified successor
evaluation and strict order decrease. The limit case certifies
`Order.IsSuccLimit (G0.eval a)`. Computation follows the rightmost tail and
uses only finite syntax. Compiled examples cover finite terms, ω + 1, ω,
ω · 2, and ε₀ in
[`OrdinalAnalysis/Examples/Gamma0SuccessorView.lean`](OrdinalAnalysis/Examples/Gamma0SuccessorView.lean).

The first executable limit-sequence family is implemented for every positive
finite multiple of ω:

```lean
G0.omegaMultipleSequence k n  -- represents ω · k + n
G0.omegaMultiple k.succ      -- represents ω · (k + 1)
```

The sequences are strictly increasing, bounded by their target, and cofinal;
`G0.omegaMultipleSequence_iSup_eval` proves supremum convergence.
`G0.ofNat` and `G0.omegaMulAddNat` build the needed canonical finite blocks
directly from syntax.

The reusable `G0.LimitSequenceData` certificate records the limit property,
sequence, strict increase, bound, and cofinality. Its `iSup_eval` theorem
derives convergence, and `satisfies` connects it to the generic classifier's
limit contract. `G0.omegaMultipleLimitSequenceData` supplies the first family.
Native examples are in
[`OrdinalAnalysis/Examples/Gamma0OmegaSequence.lean`](OrdinalAnalysis/Examples/Gamma0OmegaSequence.lean).

Canonical Veblen application is now executable:

```lean
G0.veblen : G0 → G0 → G0
G0.eval_veblen (index arg : G0) :
  G0.eval (G0.veblen index arg) =
    Ordinal.veblen (G0.eval index) (G0.eval arg)
```

The constructor uses raw comparison to choose a normal principal term or
collapse a redundant fixed-point presentation. For example,
`G0.veblen G0.zero G0.epsilonZero = G0.epsilonZero`.

For any certified argument sequence `data : G0.LimitSequenceData a`,
`data.veblenRight index` gives a certified sequence at `G0.veblen index a`.
This implements the fixed-index, limit-argument Veblen rule and preserves
strict increase, bounds, cofinality, and supremum convergence. Applying it to
the sequence at ω yields sequences at ω^ω and φ₁(ω); it can also be iterated.
Native and semantic examples are in
[`OrdinalAnalysis/Examples/Gamma0VeblenSequence.lean`](OrdinalAnalysis/Examples/Gamma0VeblenSequence.lean).

The successor-argument rule at Veblen index zero is also implemented. When
`G0.predecessor? a = some b`, `G0.omegaPowSuccSequence b` computes
the finite multiples `ω^(G0.eval b) · n`, cofinal below `ω^(G0.eval a)`.
`G0.omegaPowSuccLimitSequenceData` certifies the sequence, and
`G0.omegaPowSuccSequence_iSup_eval` proves its supremum.

The executable constructor `G0.veblenMulNat index arg n` represents
`φ_index(arg) · n`. It scales the normalized principal value, so fixed-point
cases such as `ω^ε₀ · 2 = ε₀ · 2` remain canonical.
Native examples and convergence checks for ω² and ω^(ε₀ + 1) are in
[`OrdinalAnalysis/Examples/Gamma0OmegaPowSuccessor.lean`](OrdinalAnalysis/Examples/Gamma0OmegaPowSuccessor.lean).

First-fixed-point sequences at successor Veblen indices are now executable.
If `G0.predecessor? index = some lower`, then
`G0.veblenZeroSequence lower` iterates φ_lower from zero and is cofinal
below `G0.veblen index G0.zero`. The certificate
`G0.veblenZeroLimitSequenceData` proves strict increase, boundedness,
cofinality, and supremum convergence.

This includes the tower 0, 1, ω, ω^ω, ... at ε₀ and the iteration
0, ε₀, φ₁(ε₀), ... at φ₂(0). The reusable executable iterator
`G0.veblenIterate index seed` also has verified semantic iteration and
strict-monotonicity theorems. Examples are in
[`OrdinalAnalysis/Examples/Gamma0VeblenZeroSequence.lean`](OrdinalAnalysis/Examples/Gamma0VeblenZeroSequence.lean).

Successor arguments at successor Veblen indices are implemented as well.
Given predecessor certificates for `index` and `arg`,
`G0.veblenSuccSequence lower index beta` iterates φ_lower from
φ_index(beta) + 1 and is cofinal below φ_index(arg).
`G0.veblenSuccLimitSequenceData` certifies the rule, and
`G0.veblenSuccSequence_iSup_eval` proves convergence.

The reusable executable constructor `G0.successor` preserves canonical
normal form and satisfies `G0.eval_successor`. It increments the final
finite block or appends one after the rightmost limit block.
Examples cover finite and mixed sums, fixed-point collapse, the sequence at
ε₁, and the corresponding rule at φ₂(1) in
[`OrdinalAnalysis/Examples/Gamma0VeblenSuccessorSequence.lean`](OrdinalAnalysis/Examples/Gamma0VeblenSuccessorSequence.lean).

Limit-index Veblen rules, general sum assembly, the total generic
`OrdinalClassifier` adapter, and general notation-level arithmetic remain
future work.

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

The core notation system is implemented: finite Veblen normal forms, executable comparison, verified semantics, exact range, `G0 ≃o Set.Iio Γ₀`, and a generic `OrdinalNotationSystem` adapter. Executable zero/successor/limit shape classification and certified successor predecessors are implemented. Certified executable fundamental sequences for positive finite multiples of ω are implemented. Canonical Veblen application and fixed-index, limit-argument sequence lifting are implemented. Finite principal multiplication and the index-zero successor-argument sequence rule are implemented. First-fixed-point sequences at successor indices are implemented by certified Veblen iteration. Executable canonical successors and successor-argument sequences at successor indices are implemented. Limit-index rules, general sum assembly, the full generic classifier, and general notation-level arithmetic remain future work.

Longer-term work may move beyond mathlib's existing concrete notation systems toward collapsing-function and Bachmann-Howard style notations.

## Scope

v0.3.0 does not yet add Γ₀/Veblen syntax, Gentzen's consistency proof, infinitary proof systems, cut elimination, fast-growing hierarchies, or collapsing-function systems. Its purpose is the reusable verified notation-system infrastructure on which later concrete systems can build.

## Citation and archival metadata

Citation metadata is provided in [`CITATION.cff`](CITATION.cff). Zenodo-specific release metadata is provided in [`.zenodo.json`](.zenodo.json).

Release procedures are documented in [`docs/release-v0.1.0.md`](docs/release-v0.1.0.md), [`docs/release-v0.2.0.md`](docs/release-v0.2.0.md), and [`docs/release-v0.3.0.md`](docs/release-v0.3.0.md). The archived project is available through the Zenodo DOI badge above.

See [`CHANGELOG.md`](CHANGELOG.md) for the release summary.

## License

This project is released under the [MIT License](LICENSE).
