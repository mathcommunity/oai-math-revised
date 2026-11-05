# Dependency and provenance map

The machine-readable [manifest](manifest.json) is the complete module graph. The lists below explain its construction; they do not count files as independent theorems.

| Source line | Selection | Treatment |
| --- | --- | --- |
| Owner integration at `a7e65d2102ccea27be533147dbe562024c4dca65` | All 293 non-diagnostic/nonfailed modules in `Contrib/Kotler`, plus `SpinPlaneCovariance` | 294 byte-identical source copies. |
| FCP physical endpoint at `94b6d14ad7e946747b3c0b2c51f42654755151a7` | Full transitive source-import closure of the physical Hamiltonian/eigenpair comparison, reusing ten already present owner modules | 495 additional source modules, with import-path-only adaptation. |
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

Three owner files are retained in the research repository and excluded here:

- `SU2BFSSPairedSpin9V10HF10AWSubtypeCoercionInterfaceDiagnostic`: a proof-interface diagnostic.
- `SU2BFSSPairedSpin9V10HF10DOriginalGammaPrivateScopeMicroProbe`: a two-cell private-visibility diagnostic.
- `SU2BFSSPairedSpin9V10HF10ExactGamma8PositiveAnchorProbe`: the older failed full anchor candidate; later source-exact work uses a different proof interface.

They are not required by any selected mathematical import. Failed and diagnostic sources are not silently promoted because they occur beside later successful files.

The original FCP snapshot also contains experiments outside the selected operator dependency graph. [outside-operator-closure.json](outside-operator-closure.json) records them as outside this import closure, without inferring either acceptance or rejection from their filenames. The package's scope is the complete current owner integration plus the full physical result line presented in v0.4.0, rather than every historical experiment in FCP.

The existing run history, all old workflows, recovery trials and chronological handoffs remain in the research repositories. Only one reproducible source-package build workflow is proposed here.

One direct FCP import of the deprecated `Mathlib.Data.Complex.Basic` wrapper is redirected to `Mathlib.Basic.Complex.Basic`, the exact public import of that wrapper at the pinned Mathlib revision. No declaration or proof body changes. Every other explicit Mathlib import was checked against that revision; one transient lookup failure was rechecked successfully.
