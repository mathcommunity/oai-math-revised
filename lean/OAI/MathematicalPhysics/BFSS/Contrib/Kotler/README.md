# BFSS operator and spin-geometry contribution

This package brings together the reusable source modules behind Evan T. Kotler's AI-assisted BFSS research, including the operator and local-geometry lines described in [the v0.4.0 report](https://doi.org/10.5281/zenodo.23969575). It is intended as one coherent code contribution. Its branch is built on `contribution/bfss-v040-follow-up-20261105` at `37af0591d8c968e6232968b0951639798a2d7028`, carrying the existing manuscript NOTES.md edit from [PR #75](https://github.com/mathcommunity/oai-math-revised/pull/75). PR #75 itself is unchanged.

**Integration status:** assembled and statically checked; the complete fresh Lean integration build is pending. Historical successful research runs are evidence for their stated sources and procedures, not a substitute for checking this combined import graph. This package is not peer reviewed and does not certify the original manuscript's conclusions.

## Mathematical organization

Import paths in the table are relative to `OAI.MathematicalPhysics.BFSS.Contrib.Kotler`.

| Entry point | Content and intended use | Boundary |
| --- | --- | --- |
| `Concrete` | Explicit gamma/color/Fock constructions and source spin-plane covariance; concrete inputs for later representation arguments. | These pieces are not by themselves a complete physical model or spectral theorem. |
| `Representations` | Source Clifford/PBW machinery, paired-label Lie representations, special-orthogonal one-parameter flows and quotient comparisons. | A one-parameter flow or Lie map does not supply a global physical Spin(9) lift. |
| `LocalGeometry` | Exact two-sign natural-action fibers, local source reconstruction, an open identity chart, its ambient derivative-range Lie algebra and gamma comparison, and translated topological charts. | Smooth atlas compatibility, a formal source tangent identification and the full manifold differential remain open. |
| `PhysicalOperators` | The dependency closure of the independent/reference charge graph, natural-domain Hamiltonian graph and existing-eigenpair comparisons. | Explicit matching data remain premises; no eigenpair existence is inferred. |
| `All` | The entire selected package. | Imports the interfaces above without adding a new mathematical conclusion. |

The four thematic entry points are views of one dependency graph, not separate submission batches. Existing filenames and declaration namespaces are retained so source references remain traceable. Some source comments describe the historical stage at which a file was written; the current integration status is stated here and in the exact build record.

## Operator hypotheses and interpretation

The principal physical comparisons take a finite-dimensional complex inner-product space E; 48 symmetric generators satisfying CAR; literal color and gamma matching with the reference model; and a supplied complex-linear isometric equivalence J to the reference fermion space, intertwining each generator. Their input/output unitaries act on the actual gauge-physical Hilbert spaces and the sixteen-output Hilbert sum.

The independent charge is defined from its own physically constrained smooth graph and closure, not by conjugating the reference operator. In the normalized independent Hamiltonian, J supplies the physical completeness construction in the source. The Hamiltonian uses the true two-stage natural domain of `(1/16) T†T`. The graph comparison preserves that domain. An iff between eigenpair predicates transfers a supplied witness; it does not produce one.

The reference Hamiltonian is a specified Lean operator. Its complete identification with the October 5 prose Hamiltonian remains a separate source-to-manuscript obligation. The nine-vector source action, sixteen-real gamma target and 48-real fermionic label action are distinct objects throughout.

## Source and dependency inventory

The package selects **792 existing source modules**: 294 from the owner integration and 498 from the physical-operator dependency closure. It supplies six small thematic/aggregate import modules plus one declaration-audit file. These numbers count source files, not independent discoveries or new theorems.

- [manifest.json](manifest.json) records each source repository, immutable commit, original path/blob, destination blob, import dependencies, adaptation and a topological build order.
- [THEOREMS.md](THEOREMS.md) is a browsable index of named theorem/lemma source locations.
- [declarations.json](declarations.json) is a lexical inventory of 2,939 named public declaration candidates and their source locations. The Lean-generated audit, rather than this lexical count, determines which declarations elaborate and what axioms they use.
- [DEPENDENCIES.md](DEPENDENCIES.md) explains reuse, exclusions and the recovered cross-commit sources.
- [CLAIMS.md](CLAIMS.md) gives a compact route from the report's headline claims to declarations and modules.

The 294 owner modules are byte-identical to the pinned research snapshot. The 498 FCP modules adapt import paths to the contribution namespace. After the first integration run reported a style-linter failure, 42 proof-instance tactics in 24 FCP files were changed from `letI`/`haveI` to `let`/`have`, as required by the pinned Mathlib linter for proposition proofs. The next run exposed a transitive import lost through owner-module reuse; three direct imports and three existing FCP prerequisites restore that visibility. A subsequent deprecation failure prompted replacement of 30 deprecated API references in 15 FCP files with the declarations prescribed by pinned Mathlib. DEPENDENCIES.md and the manifest record these changes. Declaration types, mathematical definitions, term-mode instances and proof resource limits are retained; proof text changes are restricted to the documented instance syntax and API references. Eight FCP prerequisites were absent from the selected operator snapshot because its successful gates fetched them from separate commits. This package includes those pinned sources with the documented adaptations, eliminating that source-availability dependence on historical caches.

No experimental workflow archive, failed candidate, interface diagnostic or chronological handoff is part of this proposed code change. The explicit excluded files and outside-closure classification are in the source inventory. Supporting mathematical lemmas remain when they are part of the selected source dependency graph.

## Reproduce the combined check

The upstream Lake configuration, Lean 4.34.1 and Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612` remain unchanged. From the repository root:

```sh
python3 lean/OAI/MathematicalPhysics/BFSS/Contrib/Kotler/tools/check_bundle.py
cd lean
lake exe cache get
cd ..
python3 lean/OAI/MathematicalPhysics/BFSS/Contrib/Kotler/tools/build_bundle.py --logs /tmp/bfss-bundle-check
```

The build script first compiles unchanged upstream imports and resolves Lake's environment once. It then invokes Lean directly in that environment, deleting and freshly producing every selected contribution object in dependency order with `autoImplicit=false`, warnings as errors and an 840-second per-module bound, without changing any source proof limits. Finally it checks all thematic imports together and runs `Audit.lean`, requiring exactly the recorded declaration reports and only `propext`, `Classical.choice`, and `Quot.sound`. A missing object, source hash, import, declaration report or successful process exit fails the check. Historical cached contribution objects are not restored. Lake setup warnings have their own log; Lean diagnostics still fail compilation and the declaration audit.

On the contribution branch, `check_bundle.py --check-contribution-base` additionally checks ancestry from the follow-up commit and the exact inherited NOTES.md blob. That branch-specific preparation check is not imposed on later community merges or notes edits.

The GitHub workflow preserves exact-head logs and inventories on failure as well as success. Its job budget covers the complete source graph; it is not a relaxation of a theorem's assumptions or proof settings. A passing build establishes the specified compilation/axiom check at that head, not physical interpretation or independent human mathematical review.

Compilation records each module as passed, failed or blocked. Failed modules have their output objects removed; their dependants are skipped. Independent modules continue so one run can expose independent errors. Any failure or blocked dependency fails the whole build before the combined axiom audit. The workflow also runs fake-compiler control-flow fixtures; those test the runner's rejection behavior, not any Lean theorem. `module-progress.jsonl` preserves progress before completion and `module-results.json` records final compilation counts.

## Attribution and assistance

This is Evan T. Kotler's contribution assembled from the etblink/math integration and Foundational Convergence Program research. Substantial ChatGPT/Codex assistance was used in source exploration, code and audit development/repair, dependency analysis and exposition. The human author directed the project and its publication decisions; no unperformed independent human proof audit is attributed to him.

Original OpenAI BFSS definitions and Mathlib/Lean infrastructure retain their authorship and licenses. Existing source notices are preserved; this contribution follows the destination repository's Apache-2.0 contribution context. The provenance records identify adapted original-source material explicitly.
