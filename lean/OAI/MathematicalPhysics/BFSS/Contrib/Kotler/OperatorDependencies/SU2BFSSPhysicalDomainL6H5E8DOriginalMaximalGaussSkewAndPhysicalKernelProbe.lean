import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8COriginalCoreGaussSkewSymmetryProbe

/-!
L6H5E8D — extend skew-symmetry from original BFSS SmoothCore
to the actual source unitary group's maximal strong derivative
domain, and identify the original physical fixed subspace as
a subset of the source infinitesimal color Gauss kernel.

Qualified inputs:
- H5E8B exact maximal differentiability domain, generator,
  and core-dense source action;
- H5E8C generic abstract skew theorem for true unitary orbits;
- H5B true original physical gauge orbit derivative = zero;
- L6G7Z actual source FullL2 linear unitary equivalence.

This does NOT equate the maximal generator domain with SmoothCore,
prove its closedness, essential skew-adjointness, or a BFSS
Hamiltonian spectral property. No surrogate Fock representation,
new axioms or changes to signs and pullback conventions.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8D
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
-- #316: pairedGaugeData is in the qualified original GaugeG4J namespace.
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6G7Z
open FCP.BFSSSU2PhysicalDomainL6H5A
open FCP.BFSSSU2PhysicalDomainL6H5B
open FCP.BFSSSU2PhysicalDomainL6H5E8B
open FCP.BFSSSU2PhysicalDomainL6H5E8C

/-- Every member of the MAXIMAL source color-domain really has
a strong real-time derivative whose value is exactly the
defined source generator. This is the domain definition, not
an added smoothness assumption. -/
theorem actualOriginalColorGenerator_hasDerivAt
    (c : ColorIndex 2)
    (v : actualOriginalFullL2ColorInfinitesimalDomain c) :
    HasDerivAt
      (fun t : ℝ =>
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c t) (v : FullL2 2))
      (actualOriginalFullL2ColorInfinitesimalGenerator c v) 0 := by
  change HasDerivAt
    (fun t : ℝ =>
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c t) (v : FullL2 2))
    (deriv (fun t : ℝ =>
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c t) (v : FullL2 2)) 0) 0
  exact v.property.hasDerivAt

/-- The exact source SU2 infinitesimal generator is
skew-symmetric on ALL pairs of vectors in its MAXIMAL
strong differentiability domain (strictly stronger than
the independently accepted SmoothCore result). -/
theorem actualOriginalColorGenerator_maximalDomain_skew_inner
    (c : ColorIndex 2)
    (u v : actualOriginalFullL2ColorInfinitesimalDomain c) :
    inner ℂ (u : FullL2 2)
        (actualOriginalFullL2ColorInfinitesimalGenerator c v) +
      inner ℂ (actualOriginalFullL2ColorInfinitesimalGenerator c u)
        (v : FullL2 2) = 0 := by
  let U : ℝ → FullL2 2 ≃ₗᵢ[ℂ] FullL2 2 :=
    fun t => actualOriginalFullL2GaugeUnitaryEquiv
      (sourcePlusIGaugeCurve c t)
  have h0u : U 0 (u : FullL2 2) = (u : FullL2 2) := by
    change actualOriginalFullL2GaugePairCLM
      (sourcePlusIGaugeCurve c 0) (u : FullL2 2) = (u : FullL2 2)
    exact actualOriginalFullL2ColorCurve_zero c (u : FullL2 2)
  have h0v : U 0 (v : FullL2 2) = (v : FullL2 2) := by
    change actualOriginalFullL2GaugePairCLM
      (sourcePlusIGaugeCurve c 0) (v : FullL2 2) = (v : FullL2 2)
    exact actualOriginalFullL2ColorCurve_zero c (v : FullL2 2)
  have hu :
      HasDerivAt (fun t : ℝ => U t (u : FullL2 2))
        (actualOriginalFullL2ColorInfinitesimalGenerator c u) 0 := by
    change HasDerivAt
      (fun t : ℝ =>
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c t) (u : FullL2 2))
      (actualOriginalFullL2ColorInfinitesimalGenerator c u) 0
    exact actualOriginalColorGenerator_hasDerivAt c u
  have hv :
      HasDerivAt (fun t : ℝ => U t (v : FullL2 2))
        (actualOriginalFullL2ColorInfinitesimalGenerator c v) 0 := by
    change HasDerivAt
      (fun t : ℝ =>
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c t) (v : FullL2 2))
      (actualOriginalFullL2ColorInfinitesimalGenerator c v) 0
    exact actualOriginalColorGenerator_hasDerivAt c v
  exact abstract_unitary_orbit_derivatives_skew
    U (u : FullL2 2) (v : FullL2 2)
      (actualOriginalFullL2ColorInfinitesimalGenerator c u)
      (actualOriginalFullL2ColorInfinitesimalGenerator c v)
    h0u h0v hu hv

/-- Every original gauge-PHYSICAL FullL2 vector is in the
actual original color Gauss generator domain, for each color. -/
theorem actualOriginalPhysical_mem_colorGeneratorDomain
    (c : ColorIndex 2) (v : FullL2 2)
    (hv : v ∈ pairedGaugeData.physicalSpace) :
    v ∈ actualOriginalFullL2ColorInfinitesimalDomain c := by
  change DifferentiableAt ℝ
    (fun t : ℝ =>
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c t) v) 0
  exact (actualOriginalPhysicalColorCurve_hasDerivAt_zero c v hv).differentiableAt

/-- TRUE fixed physical vectors have ZERO infinitesimal
source SU2 color generator. This is only the implication
physical => zero; its converse is not asserted. -/
theorem actualOriginalPhysical_colorGenerator_eq_zero
    (c : ColorIndex 2) (v : FullL2 2)
    (hv : v ∈ pairedGaugeData.physicalSpace) :
    actualOriginalFullL2ColorInfinitesimalGenerator c
      ⟨v, actualOriginalPhysical_mem_colorGeneratorDomain c v hv⟩ = 0 := by
  change deriv
    (fun t : ℝ =>
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c t) v) 0 = 0
  exact (actualOriginalPhysicalColorCurve_hasDerivAt_zero c v hv).deriv

#print axioms actualOriginalColorGenerator_hasDerivAt
#print axioms actualOriginalColorGenerator_maximalDomain_skew_inner
#print axioms actualOriginalPhysical_mem_colorGeneratorDomain
#print axioms actualOriginalPhysical_colorGenerator_eq_zero
#check @actualOriginalColorGenerator_maximalDomain_skew_inner
#check @actualOriginalPhysical_colorGenerator_eq_zero

end
end FCP.BFSSSU2PhysicalDomainL6H5E8D
