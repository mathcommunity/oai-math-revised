# Integration record

## Candidate scope

The branch is based on community main `30cd1e55f058a163f0816c2026fb55f6c4426ea6`. It proposes additions only: the source package, its documentation/inventories, and one reproducible build workflow. No existing upstream mathematical source, toolchain, Lake configuration, catalogue or manuscript is modified. Report-link PR #75 is separate.

## Completed preparation checks

- The production graph contains 789 source modules and is acyclic, with no missing contribution imports.
- All 294 owner source modules retain their exact original bytes. The 495 FCP sources preserve declaration/proof bodies; imports alone are adapted. Eight recovered sources match the Git blobs pinned by their historical workflows.
- Every explicitly imported Mathlib module was checked at the pinned revision. One deprecated import wrapper is redirected to its canonical public import. A transient lookup failure for Lie.Subalgebra was retried successfully.
- The lexical declaration index has 2,934 named public candidates, including 2,370 theorems/lemmas, with no duplicate names found. Those are source-index counts, not independent mathematical results or a compiler acceptance claim.
- The selected sources contain no explicit sorry/admit/axiom tokens after comment stripping. This lexical check does not replace the compiler's axiom reports.
- The package preflight checks every destination Git blob, the dependency order and the pinned toolchain/Mathlib values.
- Validator fixtures accept a complete permitted-axiom inventory and reject a forbidden axiom, a missing declaration and a Lean diagnostic. These are validator tests, not actual Lean compilation results.
- Workflow YAML, shell blocks and Python syntax checks pass. Headline source locators in CLAIMS.md resolve to files in the package.
- The diff is restricted to the selected additions. Existing trailing whitespace in three historical source files is retained for source-byte identity; no warning suppression is added. Generated documentation whitespace is cleaned separately.

## Fresh Lean build status

The complete combined build is **pending**. Lean 4.34.1 was installed locally, but its executable fails at startup with “failed to locate application” before any Lean source is elaborated; Lake similarly cannot locate its installation. No local source-compile result is inferred from that environment failure, and no proof limits or source assumptions were changed to work around it.

The candidate GitHub workflow uses the established Linux/elan setup, restores the pinned Mathlib cache, rebuilds existing upstream dependencies, then freshly compiles every selected contribution module in dependency order with warnings as errors. It uses no historical contribution-object caches. The combined import and complete declaration/axiom audit follow. Exact-head logs are retained for either outcome.

Historical source gates remain evidence for their own exact sources and procedures. They do not stand in for a successful run of this newly assembled graph. Update this record with the candidate commit, run and actual terminal result before recommending upstream submission.

No new mathematical conclusion, completed BFSS spectral proof or independent human peer review is claimed by this packaging work.
