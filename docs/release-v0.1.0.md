# v0.1.0 release procedure

This document is the release checklist and copy-ready release note for the first ε₀ milestone.

## Release identity

- **Tag:** `v0.1.0`
- **Package version:** `0.1.0`
- **Suggested title:** `lean-ordinal-analysis v0.1.0: Verified ε₀ notation system`
- **Target branch:** `main`
- **Prerelease:** no
- **Lean:** `v4.34.1`
- **mathlib:** `v4.34.1`

PR #20, which introduces fundamental sequences, is intentionally outside this release.

## Pre-release checklist

Before creating the GitHub release:

1. Merge the release-preparation PR.
2. Confirm the final `main` CI run is green and lint-clean.
3. Confirm `lean-toolchain` contains `leanprover/lean4:v4.34.1`.
4. Confirm `lakefile.toml` pins mathlib `v4.34.1`.
5. Confirm `lake-manifest.json` records the v4.34.1 mathlib commit.
6. Confirm `lakefile.toml` still reports version `0.1.0`.
7. Confirm `CITATION.cff` and `.zenodo.json` contain the intended creator metadata.
8. If using Zenodo's GitHub integration, make sure this repository is enabled there before publishing the GitHub release.

No DOI is committed before the archive exists.

## Suggested GitHub release notes

### v0.1.0 - Verified ε₀ notation system

This is the first release of `lean-ordinal-analysis`.

The release provides a finite, executable Cantor-normal-form notation system in Lean 4 and proves that its canonical notation type has order type exactly ε₀.

#### Highlights

- recursive raw syntax `E0Term`;
- executable normal-form checking;
- executable syntactic comparison;
- canonical notation type `E0`;
- verified linear order;
- semantic interpretation into mathlib `Ordinal`;
- comparison soundness and completeness;
- injective semantic map and order embedding;
- raw interoperability with mathlib `ONote`;
- canonical order isomorphism `E0 ≃o NONote`;
- ordinal addition, subtraction, multiplication, and exponentiation on `E0`;
- semantic correctness theorems for those operations;
- exact completeness below ε₀:
  ```lean
  E0.range_eval_eq_Iio_epsilon_zero :
    Set.range E0.eval = Set.Iio ε₀
  ```

The executable comparator is defined on finite syntax and does not use abstract ordinal comparison. Mathlib's `ONote`/`NONote` machinery is used as an interoperability and arithmetic backend only after the project's independent comparison theory has been verified.

#### Toolchain

- Lean v4.34.1
- mathlib v4.34.1

#### Documentation

See `docs/api.md` for the API guide and `docs/design.md` for the original ε₀ design.

Fundamental sequences are reserved for the next development milestone.

## Zenodo archival

Zenodo supports both `CITATION.cff` and `.zenodo.json`. Because this repository includes both, `.zenodo.json` is the metadata source Zenodo will use for GitHub release archiving, while `CITATION.cff` remains useful to GitHub's citation UI.

After publishing the GitHub release:

1. Verify that Zenodo creates the software record for `v0.1.0`.
2. Verify the creator name and ORCID.
3. Verify title, version, description, and keywords.
4. Record both:
   - the **version DOI** for v0.1.0;
   - the **concept DOI** for the software project across versions.
5. Make a small follow-up metadata PR:
   - add the v0.1.0 DOI to `CITATION.cff`;
   - add a Zenodo DOI badge/link to `README.md`;
   - optionally document the concept DOI separately for version-independent citation.

Do not invent or pre-reserve a DOI in the repository metadata unless Zenodo itself has issued it.

## Release boundary

The release commit should contain the complete v0.1.0 ε₀ system through `Completeness.lean`.

Do not merge PR #20 into the v0.1.0 release commit. PR #20 begins the fundamental-sequence work for the next milestone.
