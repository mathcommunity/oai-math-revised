import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B10CFullHaarCoreCompatibilityAndDensityProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AZOriginalPhysicalChargeDomainDensityReductionProbe

/-!
# L6H5E8BA — genuinely original physical charge operator unconditional domain density

PROSPECTIVE, NOT QUALIFIED until a strict jointly pinned Lean gate compiles
both independently accepted chains in ONE proof environment.

- Original D2B10C / Gate #47 proves the source SU(2) Haar result
  G.coreNormClosure = G.physicalSpace at N=2.
- Original L6H5E8AZ / strict Gate #2 proves density of the true
  L6H5E8AY physical Hilbert charge operator's natural domain
  conditional on precisely that original core-norm closure equality.

This module discharges the conditional premise without a new axiom,
substitute gauge representation, altered source charge, or a claim
about the manuscript's independent Clifford realization.

This does NOT establish an adjoint, T†T Hamiltonian, operator equality
with historical D2B28, point spectrum, or mass gap.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8BA
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2B10C
open FCP.BFSSSU2PhysicalDomainL6H5E8AY
open FCP.BFSSSU2PhysicalDomainL6H5E8AZ
open Set

/-- At the exact source SU(2) color rank N=2, the natural domain of
the original physical Hilbert/PiLp-sixteen charge operator is dense
in the genuine original gauge-invariant physical Hilbert space.

The proof uses the ORIGINAL source Haar theorem, not an assumption of
physical-core density nor a deformed-model alias. -/
theorem originalMinimalPhysicalHilbertChargeColumn_domain_dense_unconditional
    (M : AlgebraData 2) (G : M.GaugeData) :
    Dense ((originalMinimalPhysicalHilbertChargeColumn M G).domain :
      Set G.physicalSpace) := by
  exact originalMinimalPhysicalHilbertChargeColumn_domain_dense_of_coreNormClosure_eq
    M G (sourceCoreNormClosure_eq_physical_unconditional M G)

#print axioms originalMinimalPhysicalHilbertChargeColumn_domain_dense_unconditional

end
end FCP.BFSSSU2PhysicalDomainL6H5E8BA
