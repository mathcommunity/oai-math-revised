# Integration record

## Candidate scope

The branch is based on `contribution/bfss-v040-follow-up-20261105` at `37af0591d8c968e6232968b0951639798a2d7028`. It carries the existing BFSS NOTES.md edit, whose Git blob is `d65cd421a737c0b87511540f72dece14ef76996a`. Relative to that follow-up commit, it adds the source package, its documentation/inventories, and one reproducible build workflow. No existing upstream mathematical source, toolchain, Lake configuration, catalogue or manuscript is modified. The notes-only PR #75 remains unchanged.

## Completed preparation checks

- The production graph contains 792 source modules and is acyclic, with no missing contribution imports.
- All 294 owner source modules retain their exact original bytes. The 498 FCP sources adapt imports. The style repair described below changes only 42 proof-instance tactic keywords in 24 files; theorem statements, term-mode instances, data-valued definitions and all other proof text are retained. The subsequent dependency repair adds imports and three existing FCP sources, without changing proof bodies. Eight recovered originals match the Git blobs pinned by their historical workflows; the manifest records destination adaptations separately.
- Every explicitly imported Mathlib module was checked at the pinned revision. One deprecated import wrapper is redirected to its canonical public import. A transient lookup failure for Lie.Subalgebra was retried successfully.
- The lexical declaration index has 2,939 named public candidates, including 2,373 theorems/lemmas, with no duplicate names found. Those are source-index counts, not independent mathematical results or a compiler acceptance claim.
- The selected sources contain no explicit sorry/admit/axiom tokens after comment stripping. This lexical check does not replace the compiler's axiom reports.
- The package preflight checks every destination Git blob, the dependency order and the pinned toolchain/Mathlib values.
- Validator fixtures accept a complete permitted-axiom inventory and reject a forbidden axiom, a missing declaration and a Lean diagnostic. These are validator tests, not actual Lean compilation results.
- Workflow YAML, shell blocks and Python syntax checks pass. Headline source locators in CLAIMS.md resolve to files in the package.
- Repair checks confirm all 792 source hashes, the follow-up ancestor and the unchanged notes blob. Before the subsequent import-only repair, reversing the 42 recorded tactic-keyword substitutions reproduced the previous contribution sources exactly. A runner fixture confirms that a nonzero compiler-like process still fails and its diagnostic reaches the visible log; this fixture is not Lean build evidence.
- The import repair preserves existing and restored proof bodies. The lexical reference check finds no unavailable indexed FCP declaration or namespace, `All` reaches all 792 source modules, and all 2,939 declaration source locators resolve. Updated axiom-report fixtures cover the expanded inventory and still reject a forbidden axiom, missing report and diagnostic.
- The diff is restricted to the selected additions. Existing trailing whitespace in three historical source files is retained for source-byte identity; no warning suppression is added. Generated documentation whitespace is cleaned separately.

## Fresh Lean build status

The repaired complete build is **pending**. The first integration [run #41976747157](https://github.com/etblink/math/actions/runs/41976747157) tested `f67e17131e65a8672c4b88ed9c8491e536fc2801` and failed. Its preflight, pinned Lean/Mathlib restoration and upstream dependency build succeeded. Six contribution modules compiled before the seventh, M3E complex Clifford PBW, failed at line 48: `linter.style.haveILetI` rejects a tactic `letI` inside a proposition proof under warnings-as-errors. The module's two axiom reports contained only the permitted standard axioms, but its process failed; neither that module nor the full package is accepted by this run.

The repair changes `letI`/`haveI` to the pinned linter's prescribed `let`/`have` only at top-level tactic positions inside proposition proofs. Its rationale is documented in Mathlib's pinned `Mathlib/Tactic/Linter/HaveILetI.lean`: ordinary Lean 4 binders register local instances, and proof irrelevance makes inlining unnecessary. The same identified pattern is repaired together rather than waiting for repeated runs to report each occurrence. The original sources remain linked by immutable provenance.

The failed run also showed repeated Lake package-configuration warnings and approximately eight seconds of setup for each `lake env lean` invocation. The runner now resolves the Lake environment once, records setup warnings separately and invokes the same Lean executable directly for each fresh module and the audit. This avoids repeated configuration work and keeps administrative warnings out of the Lean-only axiom report. Compiler warnings remain errors; no linter or proof checks are suppressed. Failed compiler output is now printed directly in the job log as well as preserved in artifacts.

The earlier local Lean installation failed at startup with “failed to locate application” before source elaboration. The successful GitHub Lean startup establishes that the first run's later failure was the reported source-style diagnostic, not that local host limitation. No local source-compile result is inferred.

The next [run #41979326894](https://github.com/etblink/math/actions/runs/41979326894) tested `0b971adad47c4f238c237d48daffa6af3be1d532`. Its source and follow-up-ancestry checks, dependency restoration and upstream build passed. Seven contribution modules, including repaired M3E, compiled. M3F then failed because `OAI.BFSSQuantum`, `Fermion` and `colorDim` were unavailable through its imports. Its failed elaboration printed `sorryAx` for the unresolved Fock theorem, and the compiler's nonzero exit correctly stopped the build. That failed theorem is not an accepted result.

The smaller owner PBW dependency had removed an implicit BFSS core import. A source-reference review identified two related reuse-boundary losses. Three direct imports now restore the defining core module, S1J's actual Majorana matrix and L9E4's actual Fock generator. L9E4 and its L9E2/L9E3 prerequisites are restored from the same immutable FCP snapshot; their proof bodies are unchanged. The declaration inventory, audit, topological order and outside-closure list are updated together. The source-reference review checks known FCP names and namespaces against local import reachability; it is a lexical check, not a replacement for Lean elaboration.

The workflow now fetches full commit ancestry so the branch-base check also works for pull-request merge commits and further repair commits. This changes neither the selected source graph nor any proof setting. The complete repaired compilation and axiom audit remain pending.

The candidate GitHub workflow uses the established Linux/elan setup, restores the pinned Mathlib cache, rebuilds existing upstream dependencies, then freshly compiles every selected contribution module in dependency order with warnings as errors. It uses no historical contribution-object caches. The combined import and complete declaration/axiom audit follow. Exact-head logs are retained for either outcome.

Historical source gates remain evidence for their own exact sources and procedures. They do not stand in for a successful run of this newly assembled graph. Update this record with the candidate commit, run and actual terminal result before recommending upstream submission.

No new mathematical conclusion, completed BFSS spectral proof or independent human peer review is claimed by this packaging work.
