import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4B1BNativeNamedSourceAmbientGraphForward
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4B1ASourceNamedNativeGraphMembership

/-!
BFSS M4F9 H4B1C — FINAL native physical source-independent FORWARD
charge graph inclusion, strictly by composition of the qualified,
opaque original named 17-slot ambient image H4B1B, qualified source-
only AY graph membership H4B1A, and H3B2 native AY graph equality.
No re-elaboration of DE4 graph image or original AY source definitions.
Not the reverse direction, natural-domain equality, adjoint or H.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H4B1CNativeSourceGraphForward
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open FCP.M4F9H2APhysicalHilbertOutputUnitary
open FCP.M4F9H2CActualE2NativeHilbertChargeColumn
open FCP.M4F9H3B1OriginalAYNativePhysicalHilbertGraphRebase
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
include color gamma hColor hGamma

/-- Genuine original AY source native graph includes every J-free
independent E2 native physical Hilbert charge graph point after input
and sixteen-output physical Hilbert unitary transport. -/
theorem nativeIndependentGraph_mem_sourceGraph
    (p : independentPhysicalSpace theta hCAR hHermitian ×
      PiLp 2 (fun _ : SpinIndex =>
        independentPhysicalSpace theta hCAR hHermitian))
    (hp : p ∈ (independentActualE2NativeHilbertChargeColumn
      theta hCAR hHermitian color gamma).graph) :
    (independentPhysicalUnitary theta hCAR hHermitian J hJ p.1,
      independentPhysicalHilbertOutputUnitary
        theta hCAR hHermitian J hJ p.2) ∈
      pairedOriginalNativePhysicalHilbertChargeColumn.graph := by
  have hnamed :
      (((independentPhysicalUnitary theta hCAR hHermitian J hJ p.1 :
          pairedGaugeData.physicalSpace) : FullL2 2),
        (fun α : SpinIndex =>
          (((independentPhysicalHilbertOutputUnitary
            theta hCAR hHermitian J hJ p.2) α :
            pairedGaugeData.physicalSpace) : FullL2 2))) ∈
        (pairedGaugeData.deformedModelGraph 1 0 :
          Set (FullL2 2 × (SpinIndex → FullL2 2))) :=
    FCP.M4F9H4B1BNativeNamedSourceAmbientGraphForward.nativeIndependentGraph_mem_namedSourceAmbient
      theta hCAR hHermitian color gamma J hColor hGamma hJ p hp
  have hnative :
      (independentPhysicalUnitary theta hCAR hHermitian J hJ p.1,
        independentPhysicalHilbertOutputUnitary
          theta hCAR hHermitian J hJ p.2) ∈
      pairedOriginalPhysicalHilbertChargeGraph :=
    (FCP.M4F9H4B1ASourceNamedNativeGraphMembership.pairedNativeSourcePhysicalGraph_mem_source_iff
      (independentPhysicalUnitary theta hCAR hHermitian J hJ p.1,
        independentPhysicalHilbertOutputUnitary
          theta hCAR hHermitian J hJ p.2)).mpr hnamed
  rw [pairedOriginalNativePhysicalHilbertChargeColumn_graph_eq]
  exact hnative

#print axioms nativeIndependentGraph_mem_sourceGraph
end
end FCP.M4F9H4B1CNativeSourceGraphForward
