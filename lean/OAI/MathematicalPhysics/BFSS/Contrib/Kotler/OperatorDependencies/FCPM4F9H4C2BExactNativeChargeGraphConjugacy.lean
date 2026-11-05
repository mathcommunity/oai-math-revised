import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4C2A2ActualNativeReverseFromGeneric

/-!
BFSS M4F9 H4C2B — exact TWO-SIDED graph equivalence of ACTUAL
independent J-free E2 native Hilbert charge and original AY source native
physical Hilbert charge via GENUINE physical input and 16-output unitaries.
No operator is defined by transport; original source names stay fixed.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H4C2BExactNativeChargeGraphConjugacy
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open FCP.M4F9H2APhysicalHilbertOutputUnitary
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
include color gamma hColor hGamma

/-- Exact native graph iff for both independently defined charge columns.
U, V are the true physical Hilbert unitaries, not arbitrary graph maps.
No surrogate source operator or graph change. -/
theorem nativeIndependentGraph_mem_iff_sourceGraph
    (p : independentPhysicalSpace theta hCAR hHermitian ×
      PiLp 2 (fun _ : SpinIndex =>
        independentPhysicalSpace theta hCAR hHermitian)) :
    p ∈ (independentActualE2NativeHilbertChargeColumn
      theta hCAR hHermitian color gamma).graph ↔
      (independentPhysicalUnitary theta hCAR hHermitian J hJ p.1,
        independentPhysicalHilbertOutputUnitary
          theta hCAR hHermitian J hJ p.2) ∈
      pairedOriginalNativePhysicalHilbertChargeColumn.graph := by
  constructor
  · intro hp
    exact FCP.M4F9H4B1CNativeSourceGraphForward.nativeIndependentGraph_mem_sourceGraph
      theta hCAR hHermitian color gamma J hColor hGamma hJ p hp
  · intro hp
    have hrev :=
      FCP.M4F9H4C2A2ActualNativeReverseFromGeneric.nativeSourceGraph_mem_independentGraph
        theta hCAR hHermitian color gamma J hColor hGamma hJ
        (independentPhysicalUnitary theta hCAR hHermitian J hJ p.1,
          independentPhysicalHilbertOutputUnitary
            theta hCAR hHermitian J hJ p.2) hp
    have hi : (independentPhysicalUnitary
      theta hCAR hHermitian J hJ).symm
      (independentPhysicalUnitary theta hCAR hHermitian J hJ p.1) = p.1 :=
      (independentPhysicalUnitary theta hCAR hHermitian J hJ).symm_apply_apply p.1
    have ho : (independentPhysicalHilbertOutputUnitary
      theta hCAR hHermitian J hJ).symm
      (independentPhysicalHilbertOutputUnitary
        theta hCAR hHermitian J hJ p.2) = p.2 :=
      (independentPhysicalHilbertOutputUnitary
        theta hCAR hHermitian J hJ).symm_apply_apply p.2
    simpa only [hi, ho] using hrev

#print axioms nativeIndependentGraph_mem_iff_sourceGraph
end
end FCP.M4F9H4C2BExactNativeChargeGraphConjugacy
