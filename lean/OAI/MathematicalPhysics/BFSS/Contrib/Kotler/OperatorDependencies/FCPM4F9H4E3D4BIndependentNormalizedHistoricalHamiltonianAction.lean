import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4E3D4AIndependentNormalizedPhysicalHamiltonianDomain

/-!
H4E3D4B — prospective genuine partial independent normalized E2
Hamiltonian ACTION intertwining with original paired source D2B28
historical SU2 Hamiltonian under true physical Hilbert unitary U.

Unlike charge-level H4E3D3, the independent operator is the literal
H4E3D4A LinearPMap. The domain is the source-qualified BC.naturalComp
two-stage natural domain, not a total partial composition.
All H3B2 representation matching hypotheses and 1/16 preserved.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace FCP.M4F9H4E3D4BIndependentNormalizedHistoricalHamiltonianAction
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
open FCP.M4F9H4E3D4AIndependentNormalizedPhysicalHamiltonianDomain
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

/-- Genuine independent normalized physical Hamiltonian intertwines
historical H under U on all actual dependent natural-domain witnesses. -/
theorem independentNativeNormalizedPhysicalHamiltonian_action_historical :
    letI : CompleteSpace (independentPhysicalSpace theta hCAR hHermitian) :=
      FCP.M4F9H4D3AIndependentPhysicalHilbertComplete.independentPhysicalSpace_complete
        theta hCAR hHermitian J hJ
    letI : CompleteSpace pairedGaugeData.physicalSpace :=
      originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData
    ∀ (x : independentPhysicalSpace theta hCAR hHermitian)
      (hInd : x ∈ (independentNativeNormalizedPhysicalHamiltonian
        theta hCAR hHermitian color gamma J hJ).domain),
    ∃ hh : independentPhysicalUnitary theta hCAR hHermitian J hJ x ∈
        pairedSU2PhysicalHamiltonian.domain,
      pairedSU2PhysicalHamiltonian
          ⟨independentPhysicalUnitary theta hCAR hHermitian J hJ x,hh⟩ =
        independentPhysicalUnitary theta hCAR hHermitian J hJ
          ((independentNativeNormalizedPhysicalHamiltonian
            theta hCAR hHermitian color gamma J hJ) ⟨x,hInd⟩) := by
  refine
    (letI : CompleteSpace (independentPhysicalSpace theta hCAR hHermitian) :=
       FCP.M4F9H4D3AIndependentPhysicalHilbertComplete.independentPhysicalSpace_complete
         theta hCAR hHermitian J hJ;
     letI : CompleteSpace pairedGaugeData.physicalSpace :=
       originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData;
     ?_)
  intro x hInd
  let f := independentActualE2NativeHilbertChargeColumn
    theta hCAR hHermitian color gamma
  let U := independentPhysicalUnitary theta hCAR hHermitian J hJ
  have hSquare : x ∈ (naturalComp f.adjoint f).domain := by
    change x ∈ ((1 / 16 : ℂ) • naturalComp f.adjoint f).domain at hInd
    simpa only [LinearPMap.smul_domain] using hInd
  have hx : x ∈ f.domain := naturalComp_domain_le hSquare
  have hFx : f ⟨x,hx⟩ ∈ f.adjoint.domain :=
    naturalComp_apply_mem (⟨x,hSquare⟩ : (naturalComp f.adjoint f).domain)
  obtain ⟨hh,hAction⟩ :=
    FCP.M4F9H4E3D3IndependentHistoricalTrueSquareAction.independentNativeAdjointSquare_action_historical
      theta hCAR hHermitian color gamma J hColor hGamma hJ x hx hFx
  have hNaturalAction :
      (independentNativeNormalizedPhysicalHamiltonian
        theta hCAR hHermitian color gamma J hJ) ⟨x,hInd⟩ =
        (1 / 16 : ℂ) • f.adjoint ⟨f ⟨x,hx⟩,hFx⟩ := by
    change ((1 / 16 : ℂ) • naturalComp f.adjoint f) ⟨x,hSquare⟩ =
      (1 / 16 : ℂ) • f.adjoint ⟨f ⟨x,hx⟩,hFx⟩
    rw [LinearPMap.smul_apply, naturalComp_apply]
  refine ⟨hh, ?_⟩
  exact hAction.trans (congrArg U hNaturalAction.symm)

#print axioms independentNativeNormalizedPhysicalHamiltonian_action_historical
end
end FCP.M4F9H4E3D4BIndependentNormalizedHistoricalHamiltonianAction
