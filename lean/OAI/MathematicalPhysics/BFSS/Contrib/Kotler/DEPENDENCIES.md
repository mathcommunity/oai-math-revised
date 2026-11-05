# Dependency and provenance map

The machine-readable [manifest](manifest.json) is the complete module graph. The lists below explain its construction; they do not count files as independent theorems.

| Source line | Selection | Treatment |
| --- | --- | --- |
| Owner integration at `a7e65d2102ccea27be533147dbe562024c4dca65` | 290 selected modules in `Contrib/Kotler`, plus `SpinPlaneCovariance`; six diagnostics/failed candidates excluded as below | 291 byte-identical source copies. |
| FCP physical endpoint at `94b6d14ad7e946747b3c0b2c51f42654755151a7` | Full dependency closure of the physical Hamiltonian/eigenpair comparison, reusing ten already present owner modules and restoring prerequisites lost through that reuse | 498 additional source modules; import adaptations and the proposition-proof style edits below are recorded individually. |
| Cross-commit FCP prerequisites | Eight source files fetched separately by historical gates | Exact original blobs recovered and recorded individually; no cached object is substituted for source. |
| Existing upstream source | BFSS, Laughlin and other imported OAI definitions | No source modification; compiled as existing dependencies. |

The two older FCP and current owner realizations retain their original mathematical namespaces. Reuse is explicit where an owner module already supplies the imported interface; the package does not conflate the original and adapted Clifford/gamma carriers. The static graph has 789 nodes and is acyclic. A lexical declaration-name check found no duplicate named public declarations; Lean remains authoritative.

## Recovered sources

| Module suffix | Source commit | Original Git blob |
| --- | --- | --- |
| M3B original complex Clifford module | `a886b954032b36bd4eee4a4847c46d29d210255e` | `b215719469244884aa0a60c3cab9c95a448fa5f6` |
| M3C Schur and finiteness | `be6602ef0a3449f5547cfa1c5a630919027848f9` | `82bbab9232f14d7fe30b92a2643ad6ec6fd557c8` |
| M3D full Fock image | `f044008b574751d1af10878854b12a72db57710c` | `abbcf47e4d42c943a30b5899c8de3e5d515e18a3` |
| M3E complex Clifford PBW | `c2638df97aa854f82daf9c952f1e38e95d3044af` | `47d6a1606e4929ef3ccf8ac865f02310620101d9` |
| M3F finite dimensions | `e205c888b14405434521130d42cd63964ce4e560` | `93ed841193909fb42000e7e805c9f6f921977825` |
| M3G continuous-operator finrank | `f6c98e07c630a81a0888cfcd72503b48d70e7884` | `cbd709acd3a24983d27835ce06c04c65de898e55` |
| M3H Fock faithfulness | `5ee648514755ec97f81d74668e12212414b75b3c` | `66c99d5aa6697a40a7da542dc0a5b3df7702ee91` |
| M3I Clifford/Fock algebra equivalence | `beeb331836bb13a92c275f06f61337a6b97c0ada` | `300df1d7c886b636f2cfc206ac36f8b97f91d4b4` |

These pins were recovered from the relevant historical M3 gate workflows, including the M3J gate's explicit cross-commit M3I source check. The source bytes were checked against these Git blobs before adaptation. Reconstructing source availability is not a new mathematical theorem or a substitute for the combined integration build.

## Explicit exclusions

Six owner files are retained in the research repository and excluded here. The original three exclusions are:

- `SU2BFSSPairedSpin9V10HF10AWSubtypeCoercionInterfaceDiagnostic`: a proof-interface diagnostic.
- `SU2BFSSPairedSpin9V10HF10DOriginalGammaPrivateScopeMicroProbe`: a two-cell private-visibility diagnostic.
- `SU2BFSSPairedSpin9V10HF10ExactGamma8PositiveAnchorProbe`: the older failed full anchor candidate; later source-exact work uses a different proof interface.

Run #41985627014 exposed three additional historical failed candidates that the initial export inventory had included too broadly. Their current source blobs match their exact historical failed commits. No retained source imports any of them. The accepted successors also compiled in the diagnostic run:

| Excluded candidate | Exact failed gate | Retained successor and successful gate |
| --- | --- | --- |
| `SU2BFSSPairedSpin9SourceDeterminantCharacterProbe` | [#41257744030](https://github.com/etblink/math/actions/runs/41257744030) | `SU2BFSSPairedSpin9V10HF5TypedDirectDeterminantCharacterProbe`, [#41262335156](https://github.com/etblink/math/actions/runs/41262335156) |
| `SU2BFSSPhysicalDomainS1V52K1D18QOriginalSpinSpecialOrthogonalMembershipProbe` | [#40757842344](https://github.com/etblink/math/actions/runs/40757842344) | `SU2BFSSPhysicalDomainS1V52K1D18RSourceSpinSpecialOrthogonalWitnessProbe`, [#40759784027](https://github.com/etblink/math/actions/runs/40759784027) |
| `SU2BFSSPhysicalDomainS1V52K1D18V4OriginalSourceQuadraticPositiveDefiniteProbe` | [#40782788583](https://github.com/etblink/math/actions/runs/40782788583) | `SU2BFSSPhysicalDomainS1V52K1D18V4AOriginalSourcePositiveDefiniteStructuralProbe`, [#40784458583](https://github.com/etblink/math/actions/runs/40784458583) |

The manifest records the exact failed commits and matching source blobs. The representation entry point now imports these successors. This does not identify K1D18Q's predicate subgroup with the structural-witness subgroup, nor claim V4's failed concrete sum normal form from V4A's positivity result. The three failed candidates and all previous attempts remain available in research Git history.

They are not required by any selected mathematical import. Failed and diagnostic sources are not silently promoted because they occur beside later successful files.

The original FCP snapshot also contains experiments outside the selected operator dependency graph. [outside-operator-closure.json](outside-operator-closure.json) records them as outside this import closure, without inferring either acceptance or rejection from their filenames. The package's scope is the complete current owner integration plus the full physical result line presented in v0.4.0, rather than every historical experiment in FCP.

The existing run history, all old workflows, recovery trials and chronological handoffs remain in the research repositories. Only one reproducible source-package build workflow is proposed here.

One direct FCP import of the deprecated `Mathlib.Data.Complex.Basic` wrapper is redirected to `Mathlib.Basic.Complex.Basic`, the exact public import of that wrapper at the pinned Mathlib revision. That redirect changes no declaration or proof body. Every other explicit Mathlib import was checked against that revision; one transient lookup failure was rechecked successfully.

The first combined run stopped at the M3E PBW module's `letI` tactic because the pinned Mathlib `linter.style.haveILetI` rejects it in a proposition proof. Its implementation explains that Lean 4's ordinary `let`/`have` already register local instances, and the inlining difference is irrelevant inside proofs. The same narrow repair is applied to 42 tactic occurrences in 24 FCP files, with original/destination hashes and exact lines recorded in `manifest.json`. Term-mode instances, theorem statements and data-valued definitions are retained. No linter is disabled, no axiom is introduced and no proof limit is changed. The repaired package still requires a complete fresh build.

## Explicit prerequisites after module reuse

Run #41979326894 compiled M3E successfully, then exposed that M3F had relied on the original PBW chain to import the BFSS core. The smaller reused owner module does not carry that dependency. A review of named FCP references found two related import losses, repaired in the same change:

| Consumer | Restored direct import | Reason |
| --- | --- | --- |
| M3F finite dimensions | `OAI.MathematicalPhysics.BFSS.Core` | Defines the actual `Fermion` and `colorDim` used in the theorem. |
| S1V48 gauge/spin compatibility | S1J actual Majorana color action | Defines the literal source Majorana matrix and its group laws. |
| L9E5B all-vector Clifford square | L9E4 real-linear Fock generator | Restores the original normalized Fock generators and their CAR prerequisites. |

L9E4 requires the existing L9E2 and L9E3 sources. These three source modules are restored from the same pinned FCP snapshot, with only import paths adapted; their original hashes, destination hashes and imports are included in the manifest. They are removed from the outside-closure list and their declarations are included in the combined axiom audit. This restores source visibility and does not identify distinct carriers or alter theorem statements.

## Pinned Mathlib API replacements

Run #41981909444 reached the F3 recovery module after 22 contribution modules compiled, then rejected deprecated lemma names under warnings-as-errors. A lexical sweep of fully named deprecated references against the pinned Mathlib source found these eight replacement names. The first six are literal aliases to the canonical declarations; the last two have explicit replacement annotations in the pinned source. Thirty occurrences in fifteen FCP files are updated, with locations and hashes recorded in the manifest. No warning option is disabled.

| Deprecated reference | Pinned replacement |
| --- | --- |
| `ContinuousLinearMap.smul_apply` | `_root_.smul_apply` |
| `ContinuousLinearMap.add_apply` | `_root_.add_apply` |
| `ContinuousLinearMap.sum_apply` | `_root_.sum_apply` |
| `ContinuousLinearMap.mul_apply` | `_root_.mul_apply_eq_comp` |
| `ContinuousLinearMap.neg_apply` | `_root_.neg_apply` |
| `ContinuousLinearMap.sub_apply` | `_root_.sub_apply` |
| `EuclideanSpace.single_apply` | `PiLp.single_apply` |
| `EuclideanSpace.norm_single` | `PiLp.norm_single` |

The sources are [ContinuousLinearMap/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean) and [PiL2.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/InnerProductSpace/PiL2.lean). The source sweep is not a proof of complete compatibility; the fresh combined build remains authoritative.

The first `mul_apply` migration incorrectly qualified its replacement under `ContinuousLinearMap`. Run #41985627014 reported that nonexistent constant; all nine affected references now use the root declaration. The same run exposed deprecated core `if_pos`/`if_neg` names. Fifty-one remaining uses are replaced by the compiler-prescribed `_root_.ite_eq_left`/`_root_.ite_eq_right`; one redundant `if_pos rfl` simp argument is removed while retaining `simp only`. The other compiler-reported lint repairs remove two unused simp arguments, four no-op `change` tactics and one unreachable `ring` tactic. No linter is disabled and no proof limit is increased.
