import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4E3D3IndependentHistoricalTrueSquareAction
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8BCOriginalPhysicalChargeNaturalAdjointSquareProbe

/-!
BFSS H4E3D4A — genuine independent E2 normalized physical
Hilbert partial Hamiltonian, built from the ACTUAL physical charge
T_i by the source-qualified BC.naturalComp (true two-stage domain).
First strict root: its complete natural domain iff the unchanged
historical D2B28 Hamiltonian domain after actual physical U.
No invented total operator or closedness assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace FCP.M4F9H4E3D4AIndependentNormalizedPhysicalHamiltonianDomain
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6H5E8BB
open FCP.BFSSSU2PhysicalDomainL6H5E8BC
open FCP.BFSSSU2PhysicalDomainD2B28
open FCP.IndependentPhysicalSpace
open FCP.M4F9H2CActualE2NativeHilbertChargeColumn
open FCP.M4F9H3B2OriginalAYNativePhysicalHilbertChargeColumn
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

/-- The actual independent E2 normalized physical Hamiltonian:
true natural-domain Hilbert adjoint square of the actual E2
independent charge on the genuine independent physical Hilbert space. -/
noncomputable def independentNativeNormalizedPhysicalHamiltonian :
    independentPhysicalSpace theta hCAR hHermitian →ₗ.[ℂ]
      independentPhysicalSpace theta hCAR hHermitian := by
  letI : CompleteSpace (independentPhysicalSpace theta hCAR hHermitian) :=
    FCP.M4F9H4D3AIndependentPhysicalHilbertComplete.independentPhysicalSpace_complete
      theta hCAR hHermitian J hJ
  exact (1 / 16 : ℂ) •
    (naturalComp
      (independentActualE2NativeHilbertChargeColumn
        theta hCAR hHermitian color gamma).adjoint
      (independentActualE2NativeHilbertChargeColumn
        theta hCAR hHermitian color gamma))

include theta hCAR hHermitian color gamma J hColor hGamma hJ

/-- Every actual independent physical input belongs to the exact
independent normalized square domain iff its image under the actual
original physical Hilbert unitary is in the historical H domain. -/
theorem independentNativeNormalizedPhysicalHamiltonian_domain_iff_historical :
    letI : CompleteSpace (independentPhysicalSpace theta hCAR hHermitian) :=
      FCP.M4F9H4D3AIndependentPhysicalHilbertComplete.independentPhysicalSpace_complete
        theta hCAR hHermitian J hJ
    letI : CompleteSpace pairedGaugeData.physicalSpace :=
      originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData
    ∀ (x : independentPhysicalSpace theta hCAR hHermitian),
      x ∈ (independentNativeNormalizedPhysicalHamiltonian
        theta hCAR hHermitian color gamma J hJ).domain ↔
          independentPhysicalUnitary theta hCAR hHermitian J hJ x ∈
            pairedSU2PhysicalHamiltonian.domain := by
  refine
    (letI : CompleteSpace (independentPhysicalSpace theta hCAR hHermitian) :=
       FCP.M4F9H4D3AIndependentPhysicalHilbertComplete.independentPhysicalSpace_complete
         theta hCAR hHermitian J hJ;
     letI : CompleteSpace pairedGaugeData.physicalSpace :=
       originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData;
     ?_)
  intro x
  have hNative :
      x ∈ (independentNativeNormalizedPhysicalHamiltonian
        theta hCAR hHermitian color gamma J hJ).domain ↔
      (∃ hx : x ∈ (independentActualE2NativeHilbertChargeColumn
          theta hCAR hHermitian color gamma).domain,
        (independentActualE2NativeHilbertChargeColumn
          theta hCAR hHermitian color gamma) ⟨x,hx⟩ ∈
          (independentActualE2NativeHilbertChargeColumn
            theta hCAR hHermitian color gamma).adjoint.domain) := by
    change x ∈ ((1 / 16 : ℂ) •
      naturalComp
        (independentActualE2NativeHilbertChargeColumn
          theta hCAR hHermitian color gamma).adjoint
        (independentActualE2NativeHilbertChargeColumn
          theta hCAR hHermitian color gamma)).domain ↔ _
    simpa only [LinearPMap.smul_domain] using
      (naturalComp_mem_domain :
        x ∈ (naturalComp
          (independentActualE2NativeHilbertChargeColumn
            theta hCAR hHermitian color gamma).adjoint
          (independentActualE2NativeHilbertChargeColumn
            theta hCAR hHermitian color gamma)).domain ↔ _)
  exact hNative.trans
    (FCP.M4F9H4E3D2IndependentHistoricalTrueSquareDomain.independentNativeAdjointSquare_domain_iff_historical
      theta hCAR hHermitian color gamma J hColor hGamma hJ x)

#print axioms independentNativeNormalizedPhysicalHamiltonian_domain_iff_historical
end
end FCP.M4F9H4E3D4AIndependentNormalizedPhysicalHamiltonianDomain
