# Reader route from results to source

All paths below are relative to this directory, except `../../SpinPlaneCovariance.lean`, which is two levels above it. A module name or successful historical run does not remove its theorem's premises. The full types in Lean and the v0.4.0 report are the references for interpretation.

| Result | Source locator | What is supplied |
| --- | --- | --- |
| Explicit real gamma family | `SU2RealGammaProbe.lean` | Actual nine symmetric 16×16 matrices, Clifford anticommutation and an existence witness for those gamma fields. |
| Spin-plane covariance | `../../SpinPlaneCovariance.lean` | Source-defined gamma/Clifford covariance identities, with original BFSS definitions. |
| Paired 48-label representation | `SU2BFSSPhysicalDomainS1V52K1D18V7ZOriginalSpinQuotientNativeEuclideanDetOneEquivProbe.lean` and the `Representations` entry point | Clifford/PBW, orthogonal/quotient and Lie-level interfaces; does not assert a global physical Spin(9) lift. |
| Sixteen-real gamma Lie map | `SU2BFSSPairedSpin9V10HF10BBOriginalGammaCanonicalSkewLieHom.lean` (see manifest if locating by declaration) | `coordinateToOriginalGammaSkewLieHom`, the specified so(9)→so(16) Lie homomorphism. |
| Natural two-sign fibers | `SU2BFSSPairedSpin9V10HF10CUNaturalActionTwoSignFibers.lean` | Kernel and fibers on the actual source group; no target surjectivity is inferred. |
| Exact local recovery and chart | `SU2BFSSPairedSpin9V10HF10CVExactSourceRecoveryNeighborhood.lean`, `SU2BFSSPairedSpin9V10HF10CWOriginalSourceIdentityLocalChart.lean` | Recovery and inverse laws on their explicit open sets. |
| Actual derivative and range | `SU2BFSSPairedSpin9V10HF10CXIdentityChartInverseCliffordDerivative.lean`, `SU2BFSSPairedSpin9V10HF10CYIdentityChartDerivativeRange.lean` | Full ambient derivative, injectivity and range equal to the half-bivector span. |
| Range Lie algebra and gamma comparison | `SU2BFSSPairedSpin9V10HF10DCDerivativeRangeLiePackaging.lean`, `SU2BFSSPairedSpin9V10HF10DDDerivativeRangeGammaLieHom.lean` | Actual commutator closure, native skew Lie equivalence, and literal gamma restriction/composition identities. |
| Parameter derivative | `SU2BFSSPairedSpin9V10HF10CZOriginalGammaDerivativeRangeComparison.lean` | Ordinary finite-parameter derivative factorization, without assuming a source tangent identification. |
| Translated charts | `SU2BFSSPairedSpin9V10HF10DETranslatedSourceCharts.lean` | Exact translated charts and overlaps covering the source group; a topological atlas. |
| Native physical charge graph | `OperatorDependencies/FCPM4F9H4C2BExactNativeChargeGraphConjugacy.lean` | Two-sided graph comparison under the explicit CAR, symmetry, model matching and generator-preserving unitary data. |
| Complete Hamiltonian graph | `OperatorDependencies/FCPM4F9H4E3D4C4ActualIndependentHistoricalUnitaryGraphImageEquality.lean` | Image equality of complete natural-domain graphs, retaining the normalized adjoint-square construction. |
| Eigenpair transport | `OperatorDependencies/FCPM4F9H4G1BActualIndependentHistoricalNormalizableEigenpairTransfer.lean` | Equivalence of existing nonzero, domain-qualified eigenpair predicates at a specified energy; neither existential is proved. |

Historical exact test anchors include the operator runs 40075765703, 40102750658, 40143999732 and 40146023874 in Foundational-Convergence-Program, and the geometry cutoff run 41946635772 in etblink/math. The report's evidence appendix supplies exact tested commits. Those historical checks concern their own procedures and sources; the combined package must pass its own build before submission is recommended.

No result here proves positive-energy eigenstate existence, a mass gap or confinement. Smooth source-chart compatibility, a formal source tangent identification, the full manifold differential and the global physical lift remain outside the stated result set.
