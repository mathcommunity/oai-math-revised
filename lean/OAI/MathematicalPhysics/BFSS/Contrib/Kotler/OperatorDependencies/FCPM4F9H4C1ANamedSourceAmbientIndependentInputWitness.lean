import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4B1CNativeSourceGraphForward

/-!
BFSS M4F9 H4C1A — reverse source→independent graph proof, first
source-NAMED input witness only. From literal original source 17-slot
named charge graph membership, recover an actual J-free DE2 full
physical graph witness with its genuine independent physical Hilbert
input mapping EXACTLY to the specified original source physical input.

No native partial operator graph, no original AY graph unroll,
no new operator, no reverse native graph or Hamiltonian assertion.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H4C1ANamedSourceAmbientIndependentInputWitness
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open FCP.IndependentSmoothSupercharge
open FCP.IndependentFullL2GaugeTransport
open FCP.M4F9H4ANativeHilbertAmbientCoordinateTransport
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))
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
include color gamma hColor hGamma

/-- An original source named charge-graph point has a genuine J-free
DE2 physical graph preimage with the EXACT original physical input,
not merely an ambient full-L² vector or a formal closure surrogate. -/
theorem namedSourceGraph_independentFullPhysicalInput_exists
    (x : pairedGaugeData.physicalSpace)
    (y : SpinIndex → FullL2 2)
    (hsource : ((x : FullL2 2), y) ∈
      (pairedGaugeData.deformedModelGraph 1 0 :
        Set (FullL2 2 × (SpinIndex → FullL2 2)))) :
    ∃ q : independentPhysicalSpace theta hCAR hHermitian ×
      FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualPhysicalOutputs
        theta hCAR hHermitian,
      q ∈ (FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn
        color gamma theta hCAR hHermitian).graph ∧
      independentPhysicalUnitary theta hCAR hHermitian J hJ q.1 = x := by
  have himage := hsource
  rw [FCP.M4F8OriginalNamedFullPhysicalGraphDE4.pairedSourceNamedClosedGraph_eq_actualIndependentFullPhysicalGraph_image
    color gamma theta hCAR hHermitian J hColor hGamma hJ] at himage
  rcases himage with ⟨w, ⟨q, hq, hqw⟩, hw⟩
  refine ⟨q, hq, ?_⟩
  apply Subtype.ext
  have hinput := congrArg Prod.fst hw
  rw [← hqw] at hinput
  change fiberTransport J (q.1 : Lp E 2 μ) = (x : FullL2 2) at hinput
  exact (nativeInput_eq_fiberTransport theta hCAR hHermitian J hJ q.1).trans hinput

#print axioms namedSourceGraph_independentFullPhysicalInput_exists
end
end FCP.M4F9H4C1ANamedSourceAmbientIndependentInputWitness
