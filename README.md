# lean-ordinal-analysis

Executable recursive ordinal notation systems in Lean 4, with verified semantics and order types, starting with ε₀ and Γ₀.

## Goal

This project develops concrete, computable ordinal notation systems and connects them to Lean's abstract `Ordinal` theory.

The guiding separation is:

1. **finite syntax** — recursive terms that Lean can compute with;
2. **canonical notation** — normal forms equipped with decidable comparison;
3. **semantic ordinal** — an interpretation into `Ordinal`, used to verify the notation system rather than define it.

The first major target is a finite recursive notation system whose verified order type is ε₀. The second is a Veblen-style notation system of order type Γ₀.

## Initial roadmap

### v0.1 — ε₀

- raw Cantor-normal-form syntax;
- normal-form predicate;
- executable syntactic comparison;
- interpretation into `Ordinal`;
- correctness of comparison under interpretation;
- injectivity and an order embedding into `Ordinal`;
- notation-level ordinal operations;
- proof that the represented ordinals are exactly those below ε₀.

### v0.2 — fundamental sequences

- fundamental sequences for limit notations;
- monotonicity and boundedness;
- semantic convergence to the represented limit ordinal.

### v0.3 — generic notation-system API

Extract reusable abstractions only after the ε₀ implementation has exposed the right interface.

### v0.4 — Γ₀

- finite Veblen normal forms;
- executable comparison and normalization;
- interpretation via mathlib's Veblen hierarchy;
- proof that the resulting notation system has order type Γ₀.

## Scope

The early project deliberately does **not** attempt to formalize Gentzen's consistency proof, infinitary proof systems, cut elimination, or Bachmann–Howard collapsing systems. Those are possible later applications once the notation infrastructure is solid.

## Design principle

The notation systems should remain computational. In particular, comparison and normalization are defined on finite syntax and do not call out to abstract `Ordinal` comparison. The semantic interpretation into `Ordinal` certifies those algorithms.

See [`docs/design.md`](docs/design.md) for the frozen initial ε₀ design.

## Status

PR #1 establishes the Lean/mathlib scaffold and the mathematical design for the ε₀ implementation. The next development slice introduces the raw term datatype.
