# v0.2.0 release procedure

This document is the release checklist and copy-ready release note for the ε₀ fundamental-sequence milestone.

## Release identity

- **Tag:** `v0.2.0`
- **Package version:** `0.2.0`
- **Suggested title:** `lean-ordinal-analysis v0.2.0: Verified ε₀ fundamental sequences`
- **Target branch:** `main`
- **Prerelease:** no
- **Lean:** `v4.34.1`
- **mathlib:** `v4.34.1`

## Release boundary

v0.2.0 includes the complete v0.1.0 ε₀ notation system plus the fundamental-sequence development through `LimitFundamentalSequence.lean`.

The mathematical endpoint is:

- executable zero/successor/limit classification;
- canonical predecessor output for successor notations;
- canonical sequences for semantic limits;
- strict monotonicity;
- boundedness below the input notation;
- semantic cofinality;
- exact indexed-supremum convergence;
- an ergonomic limit-only API.

Generic notation-system abstractions and Γ₀/Veblen notation begin after this release.

## Pre-release checklist

Before creating the GitHub release:

1. Merge the v0.2.0 release-preparation PR.
2. Confirm the final `main` CI run is green and lint-clean.
3. Confirm `lean-toolchain` contains `leanprover/lean4:v4.34.1`.
4. Confirm `lakefile.toml` pins mathlib `v4.34.1`.
5. Confirm `lake-manifest.json` records the v4.34.1 mathlib commit.
6. Confirm `lakefile.toml` reports version `0.2.0`.
7. Confirm `LICENSE` is MIT and both `CITATION.cff` and `.zenodo.json` identify the license consistently.
8. Confirm `CITATION.cff` and `.zenodo.json` report version `0.2.0`, the intended creator name, and ORCID.
9. Confirm README and `docs/api.md` describe the v0.2.0 fundamental-sequence API.
10. Verify the repository remains enabled in Zenodo's GitHub integration before publishing the GitHub release.

No new v0.2.0 DOI should be committed before Zenodo actually creates the archive record.

## Suggested GitHub release notes

### v0.2.0 - Verified ε₀ fundamental sequences

Version 0.2.0 extends the verified executable ε₀ notation system with fundamental sequences.

#### Highlights

- executable zero/successor/limit classification via `E0.fundamentalSequence`;
- canonical predecessor output in the successor branch;
- canonical fundamental sequences in the limit branch;
- semantic certification of all classifier branches;
- strict monotonicity of limit sequences;
- every sequence entry is verified below the original notation;
- semantic cofinality below the represented limit ordinal;
- exact convergence:
  ```lean
  E0.fundamentalSequence_eq_limit_iSup_eval :
    (⨆ i, E0.eval (seq i)) = E0.eval a
  ```
- certified `E0.LimitFundamentalSequenceData`;
- ergonomic `E0.limitFundamentalSequence` API with direct monotonicity, boundedness, cofinality, and convergence theorems.

The ε₀ syntax and executable comparison remain independent project definitions. Mathlib's `ONote`/`NONote` machinery is used as a verified interoperability backend after that independent syntax and comparison theory has been established.

#### Toolchain

- Lean v4.34.1
- mathlib v4.34.1

#### Documentation

See `docs/api.md` for the v0.2.0 API guide and `docs/design.md` for the original ε₀ design.

## Zenodo archival

After publishing the GitHub release:

1. Verify that Zenodo creates the software record for `v0.2.0`.
2. Verify creator name, ORCID, title, version, description, keywords, and MIT license.
3. Record the DOI Zenodo assigns to the v0.2.0 archive.
4. Determine whether the existing DOI linked from the README is the project-level concept DOI or a version DOI before changing that link.
5. Make a small post-release metadata PR if needed:
   - add the v0.2.0 version DOI to `CITATION.cff`;
   - update or clarify the README DOI link;
   - document the concept DOI separately if appropriate.

Do not invent or pre-reserve a DOI in repository metadata.

## Post-release

After the archive is verified, the next development milestone is v0.3: extraction of a reusable generic notation-system API before beginning Γ₀/Veblen notation.
