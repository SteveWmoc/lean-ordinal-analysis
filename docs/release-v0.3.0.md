# v0.3.0 release procedure

This document is the release checklist and copy-ready release note for the generic notation-system API milestone.

## Release identity

- **Tag:** `v0.3.0`
- **Package version:** `0.3.0`
- **Suggested title:** `lean-ordinal-analysis v0.3.0: Generic verified ordinal notation systems`
- **Target branch:** `main`
- **Prerelease:** no
- **Lean:** `v4.34.1`
- **mathlib:** `v4.34.1`

## Release boundary

v0.3.0 extracts the reusable semantic architecture exposed by the completed ε₀ notation and fundamental-sequence development.

The milestone includes:

- `OrdinalNotationSystem`, a generic interface for canonical notation systems;
- generic monotonicity, injectivity, and order-embedding consequences;
- exact semantic range below an arbitrary system bound;
- the canonical order isomorphism `N ≃o Set.Iio system.bound`;
- generic zero/successor/limit classification;
- a certified `OrdinalClassifier`;
- generic successor and limit branch consequences;
- generic cofinality and indexed-supremum convergence;
- a generic ergonomic limit-sequence bundle and accessor;
- adapters packaging the existing ε₀ system and classifier into the generic API;
- compiled ε₀ examples demonstrating that the abstraction recovers the v0.1/v0.2 results.

Γ₀/Veblen notation itself is not part of this release. It is the next milestone and the first serious external test of the abstraction.

## Pre-release checklist

Before creating the GitHub release:

1. Merge the v0.3.0 release-preparation PR.
2. Confirm the final `main` CI run is green and lint-clean.
3. Confirm `OrdinalAnalysis/Examples/Epsilon0Generic.lean` builds from the root library target.
4. Confirm `lean-toolchain` contains `leanprover/lean4:v4.34.1`.
5. Confirm `lakefile.toml` pins mathlib `v4.34.1`.
6. Confirm `lake-manifest.json` records the v4.34.1 mathlib commit.
7. Confirm `lakefile.toml` reports version `0.3.0`.
8. Confirm `LICENSE` is MIT and both `CITATION.cff` and `.zenodo.json` identify the license consistently.
9. Confirm `CITATION.cff` and `.zenodo.json` report version `0.3.0`, the intended creator name, and ORCID.
10. Confirm README, `docs/api.md`, and `docs/generic-api.md` describe the v0.3.0 public surface.
11. Verify the repository remains enabled in Zenodo's GitHub integration before publishing the GitHub release.

No v0.3.0 DOI should be guessed or committed before Zenodo creates the archive record.

## Suggested GitHub release notes

### v0.3.0 - Generic verified ordinal notation systems

Version 0.3.0 turns the ε₀ development into reusable infrastructure for future ordinal notation systems.

#### Highlights

- introduce `OrdinalNotationSystem N` with semantic evaluation, an exact bound, order correctness, and completeness;
- derive semantic monotonicity, injectivity, and an order embedding generically;
- derive the exact range theorem
  ```lean
  Set.range system.eval = Set.Iio system.bound
  ```
  for every verified notation system;
- package the exact order type as
  ```lean
  system.orderIsoIio :
    N ≃o Set.Iio system.bound
  ```;
- introduce generic `ClassificationResult N` and certified `OrdinalClassifier system`;
- derive generic zero/successor/limit branch consequences;
- derive generic semantic cofinality and indexed-supremum convergence;
- introduce `OrdinalClassifier.LimitSequenceData` and the ergonomic
  ```lean
  classifier.limitSequence a hlim
  ```
  API;
- package the existing ε₀ development as `E0.notationSystem` and `E0.classifier`;
- recover
  ```lean
  E0 ≃o Set.Iio ε₀
  ```
  through the generic exact-initial-segment theory;
- add compiled examples demonstrating that ε₀ satisfies and uses the complete generic API.

The abstraction deliberately begins at canonical notation types. It does not prescribe raw syntax, normal forms, normalization, arithmetic, or a specific comparison algorithm.

#### Toolchain

- Lean v4.34.1
- mathlib v4.34.1

#### Documentation

See `docs/generic-api.md` for the generic v0.3 API, `docs/api.md` for the detailed ε₀ API, and `docs/design.md` for the original ε₀ design.

## Zenodo archival

After publishing the GitHub release:

1. Verify that Zenodo creates the software record for `v0.3.0`.
2. Verify creator name, ORCID, title, version, description, keywords, and MIT license.
3. Record the DOI assigned to the v0.3.0 archive.
4. Verify whether the README DOI badge continues to resolve through the intended project/concept record.
5. Make a small post-release metadata PR only if Zenodo-issued DOI metadata needs to be recorded or clarified.

Do not invent or pre-reserve a DOI in repository metadata.

## Post-release

The next development milestone is v0.4: finite Γ₀/Veblen notation, executable comparison, semantic certification, and an exact Γ₀ order-type theorem. Γ₀ should use the v0.3 generic interfaces wherever they genuinely fit and should expose any abstraction changes demanded by a second concrete notation system.
