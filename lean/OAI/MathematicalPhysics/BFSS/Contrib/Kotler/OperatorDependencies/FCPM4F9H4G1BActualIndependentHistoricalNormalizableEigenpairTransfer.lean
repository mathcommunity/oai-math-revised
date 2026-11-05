import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4G1AGenericUnitaryNormalizableEigenpairTransfer

/-!
BFSS M4F9 H4G1B — conditional equivalence of EXISTING nonzero,
normalizable physical Hilbert eigenvectors for ACTUAL independent E2
and pinned original historical D2B28 SU2 Hamiltonians.

The result does NOT assert there are any eigenvalues. In particular,
it does not prove positive normalizable eigenvectors or a mass gap.
All independent-to-historical representation matching is explicit.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace FCP.M4F9H4G1BActualIndependentHistoricalNormalizableEigenpairTransfer
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6H5E8BB
open FCP.BFSSSU2PhysicalDomainD2B28
open FCP.IndependentPhysicalSpace
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

/-- Equivalence of nonzero normalizable eigenpairs at each specified
complex energy: genuine independent E2 normalized partial physical
Hamiltonian iff original historical D2B28 SU2 Hamiltonian. -/
theorem independentNormalizedHamiltonian_eigenpair_exists_iff_historical
    (eigval : ℂ) :
    letI : CompleteSpace (independentPhysicalSpace theta hCAR hHermitian) :=
      FCP.M4F9H4D3AIndependentPhysicalHilbertComplete.independentPhysicalSpace_complete
        theta hCAR hHermitian J hJ
    letI : CompleteSpace pairedGaugeData.physicalSpace :=
      originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData
    (∃ (x : independentPhysicalSpace theta hCAR hHermitian)
        (hx : x ∈ (independentNativeNormalizedPhysicalHamiltonian
          theta hCAR hHermitian color gamma J hJ).domain),
        x ≠ 0 ∧
        (independentNativeNormalizedPhysicalHamiltonian
          theta hCAR hHermitian color gamma J hJ) ⟨x,hx⟩ =
            eigval • x)
      ↔ (∃ (y : pairedGaugeData.physicalSpace)
        (hy : y ∈ pairedSU2PhysicalHamiltonian.domain),
          y ≠ 0 ∧ pairedSU2PhysicalHamiltonian ⟨y,hy⟩ =
            eigval • y) := by
  refine
    (letI : CompleteSpace (independentPhysicalSpace theta hCAR hHermitian) :=
       FCP.M4F9H4D3AIndependentPhysicalHilbertComplete.independentPhysicalSpace_complete
         theta hCAR hHermitian J hJ;
     letI : CompleteSpace pairedGaugeData.physicalSpace :=
       originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData;
     ?_)
  let A := independentNativeNormalizedPhysicalHamiltonian
    theta hCAR hHermitian color gamma J hJ
  let B := pairedSU2PhysicalHamiltonian
  let U := independentPhysicalUnitary theta hCAR hHermitian J hJ
  have hDom : ∀ x : independentPhysicalSpace theta hCAR hHermitian,
      x ∈ A.domain ↔ U x ∈ B.domain := by
    intro x
    exact
      FCP.M4F9H4E3D4AIndependentNormalizedPhysicalHamiltonianDomain.independentNativeNormalizedPhysicalHamiltonian_domain_iff_historical
        theta hCAR hHermitian color gamma J hColor hGamma hJ x
  have hAction : ∀ (x : independentPhysicalSpace theta hCAR hHermitian)
      (hx : x ∈ A.domain),
      ∃ hy : U x ∈ B.domain,
        B ⟨U x,hy⟩ = U (A ⟨x,hx⟩) := by
    intro x hx
    exact
      FCP.M4F9H4E3D4BIndependentNormalizedHistoricalHamiltonianAction.independentNativeNormalizedPhysicalHamiltonian_action_historical
        theta hCAR hHermitian color gamma J hColor hGamma hJ x hx
  exact
    FCP.M4F9H4G1AGenericUnitaryNormalizableEigenpairTransfer.genericUnitaryPartialEigenpair_exists_iff
      U A B hDom hAction eigval

#print axioms independentNormalizedHamiltonian_eigenpair_exists_iff_historical
end
end FCP.M4F9H4G1BActualIndependentHistoricalNormalizableEigenpairTransfer
