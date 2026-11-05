import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4E3D4C1GenericUnitaryPartialGraphEquivalence

/-!
BFSS H4E3D4C2 — prospective literal graph membership equivalence
for the ACTUAL independent normalized E2 physical Hamiltonian
and the genuine original historical D2B28 SU2 physical Hamiltonian.

Specialize qualified generic C1 full graph iff via accepted D4A
complete two-stage natural domain equivalence and accepted D4B
actual named partial-Hamiltonian action equality. Keep original H3B2
representation matching and the genuine independent physical unitary.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace FCP.M4F9H4E3D4C2ActualIndependentHistoricalUnitaryGraphEquivalence
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

/-- Literal full graph membership iff for actual independent E2
normalized physical Hamiltonian and actual historical D2B28 source
SU2 Hamiltonian under the original physical Hilbert unitary U. -/
theorem independentNormalizedHamiltonian_graph_mem_iff_historical :
    letI : CompleteSpace (independentPhysicalSpace theta hCAR hHermitian) :=
      FCP.M4F9H4D3AIndependentPhysicalHilbertComplete.independentPhysicalSpace_complete
        theta hCAR hHermitian J hJ
    letI : CompleteSpace pairedGaugeData.physicalSpace :=
      originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData
    ∀ (x z : independentPhysicalSpace theta hCAR hHermitian),
      (x,z) ∈
        (independentNativeNormalizedPhysicalHamiltonian
          theta hCAR hHermitian color gamma J hJ).graph
      ↔ (independentPhysicalUnitary theta hCAR hHermitian J hJ x,
          independentPhysicalUnitary theta hCAR hHermitian J hJ z) ∈
            pairedSU2PhysicalHamiltonian.graph := by
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
  intro x z
  exact
    FCP.M4F9H4E3D4C1GenericUnitaryPartialGraphEquivalence.genericUnitaryPartialGraph_mem_iff
      U A B hDom hAction x z

#print axioms independentNormalizedHamiltonian_graph_mem_iff_historical
end
end FCP.M4F9H4E3D4C2ActualIndependentHistoricalUnitaryGraphEquivalence
