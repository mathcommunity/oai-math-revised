import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4E3D1NativeHistoricalExactPartialOperator
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4D4AActualNativeAdjointSquareDomain

set_option autoImplicit false
set_option maxHeartbeats 240000
namespace FCP.M4F9H4E3D2IndependentHistoricalTrueSquareDomain
noncomputable section
open OAI.BFSSQuantum OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open FCP.M4F9H2CActualE2NativeHilbertChargeColumn
open FCP.M4F9H3B2OriginalAYNativePhysicalHilbertChargeColumn
open FCP.BFSSSU2PhysicalDomainL6H5E8BB
open FCP.BFSSSU2PhysicalDomainL6H5E8BC
open FCP.BFSSSU2PhysicalDomainD2B28
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
variable (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
variable (hCAR : ∀ α β A B,
  theta α A * theta β B + theta β B * theta α A =
    (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
variable (hHermitian : ∀ α A, (theta α A).IsSymmetric)
variable (color : ColorIndex 2 → ColorMatrix 2)
variable (gamma : SpaceIndex → GammaMatrix)
variable (J : E ≃ₗᵢ[ℂ] Fermion 2)
variable (hColor : color = pairedAlgebraData.color)
variable (hGamma : gamma = pairedAlgebraData.gamma)
variable (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
include theta hCAR hHermitian color gamma J hColor hGamma hJ

/-- Exact independent E2 true two-stage square-domain equivalence
with the actual historical paired SU2 Hamiltonian via physical U. -/
theorem independentNativeAdjointSquare_domain_iff_historical :
    letI : CompleteSpace (independentPhysicalSpace theta hCAR hHermitian) :=
      FCP.M4F9H4D3AIndependentPhysicalHilbertComplete.independentPhysicalSpace_complete
        theta hCAR hHermitian J hJ
    letI : CompleteSpace pairedGaugeData.physicalSpace :=
      originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData
    ∀ (x : independentPhysicalSpace theta hCAR hHermitian),
      (∃ hx : x ∈ (independentActualE2NativeHilbertChargeColumn
          theta hCAR hHermitian color gamma).domain,
        (independentActualE2NativeHilbertChargeColumn
          theta hCAR hHermitian color gamma) ⟨x,hx⟩ ∈
          (independentActualE2NativeHilbertChargeColumn
            theta hCAR hHermitian color gamma).adjoint.domain)
        ↔ independentPhysicalUnitary theta hCAR hHermitian J hJ x ∈
            pairedSU2PhysicalHamiltonian.domain := by
  refine
    (letI : CompleteSpace (independentPhysicalSpace theta hCAR hHermitian) :=
       FCP.M4F9H4D3AIndependentPhysicalHilbertComplete.independentPhysicalSpace_complete
         theta hCAR hHermitian J hJ;
     letI : CompleteSpace pairedGaugeData.physicalSpace :=
       originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData;
     ?_)
  intro x
  let g := pairedOriginalNativePhysicalHilbertChargeColumn
  let U := independentPhysicalUnitary theta hCAR hHermitian J hJ
  have hTransport :
      (∃ hx : x ∈ (independentActualE2NativeHilbertChargeColumn
          theta hCAR hHermitian color gamma).domain,
        (independentActualE2NativeHilbertChargeColumn
          theta hCAR hHermitian color gamma) ⟨x,hx⟩ ∈
          (independentActualE2NativeHilbertChargeColumn
            theta hCAR hHermitian color gamma).adjoint.domain) ↔
        (∃ hz : U x ∈ g.domain,
          g ⟨U x,hz⟩ ∈ g.adjoint.domain) :=
    FCP.M4F9H4D4AActualNativeAdjointSquareDomain.nativeAdjointSquare_naturalDomain_iff
      theta hCAR hHermitian color gamma J hColor hGamma hJ x
  have hHistorical : U x ∈ (naturalComp g.adjoint g).domain ↔
      U x ∈ pairedSU2PhysicalHamiltonian.domain := by
    exact FCP.M4F9H4E3C2NativeSquareHistoricalFullDomainAction.nativeNormalizedSquare_naturalDomain_iff_historical
      theta hCAR hHermitian color gamma J hColor hGamma hJ (U x)
  constructor
  · intro hIndependent
    exact hHistorical.mp (naturalComp_mem_domain.mpr (hTransport.mp hIndependent))
  · intro hHist
    exact hTransport.mpr (naturalComp_mem_domain.mp (hHistorical.mpr hHist))

#print axioms independentNativeAdjointSquare_domain_iff_historical
end
end FCP.M4F9H4E3D2IndependentHistoricalTrueSquareDomain
