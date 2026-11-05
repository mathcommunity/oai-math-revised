import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4D2BGenericNativeHilbertAdjointReverse

/-! BFSS M4F9 H4D3A: completeness of the independently defined
SU2 gauge-physical Hilbert submodule, using the accepted gauge-unitary
identification only to prove closedness. -/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H4D3AIndependentPhysicalHilbertComplete
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open FCP.IndependentFullL2GaugeTransport
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
variable (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
variable (hCAR : ∀ α β A B,
  theta α A * theta β B + theta β B * theta α A =
    (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
variable (hHermitian : ∀ α A, (theta α A).IsSymmetric)
variable (J : E ≃ₗᵢ[ℂ] Fermion 2)
variable (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
include J hJ

theorem independentPhysicalSpace_complete :
    CompleteSpace (independentPhysicalSpace theta hCAR hHermitian) := by
  have hset :
      (independentPhysicalSpace theta hCAR hHermitian :
        Set (Lp E 2 (volume : Measure (Boson 2)))) =
        {v | fiberTransport J v ∈ pairedGaugeData.physicalSpace} := by
    ext v
    exact independentPhysicalSpace_iff_source
      theta hCAR hHermitian J hJ v
  have hclosed :
      IsClosed (independentPhysicalSpace theta hCAR hHermitian :
        Set (Lp E 2 (volume : Measure (Boson 2)))) := by
    rw [hset]
    exact pairedGaugeData.physicalSpace_closed.preimage
      (fiberTransportUnitary J).continuous
  exact hclosed.isComplete.completeSpace_coe

#print axioms independentPhysicalSpace_complete
end
end FCP.M4F9H4D3AIndependentPhysicalHilbertComplete
