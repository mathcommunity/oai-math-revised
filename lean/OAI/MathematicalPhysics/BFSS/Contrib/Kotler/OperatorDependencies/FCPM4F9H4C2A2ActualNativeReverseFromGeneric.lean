import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4C2A1GenericPartialGraphReverse

/-!
BFSS M4F9 H4C2A2 — specialize the KERNEL-QUALIFIED generic partial
graph reverse principle to both ACTUAL native Hilbert operators.
All original AY/H2C source names remain unchanged; no source-named
operator is defined by graph transport. Requires accepted H4C1B
source-domain recovery and H4B1C genuine independent graph forward.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H4C2A2ActualNativeReverseFromGeneric
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

/-- Original AY native source graph pulls back through genuine physical
input and 16-output Hilbert unitaries into the independent J-free
E2 native charge graph. Forward operator and reverse domain are
already qualified, no rewriting of underlying massive source graphs. -/
theorem nativeSourceGraph_mem_independentGraph
    (p : pairedGaugeData.physicalSpace ×
      PiLp 2 (fun _ : SpinIndex => pairedGaugeData.physicalSpace))
    (hp : p ∈ pairedOriginalNativePhysicalHilbertChargeColumn.graph) :
    ((independentPhysicalUnitary theta hCAR hHermitian J hJ).symm p.1,
      (independentPhysicalHilbertOutputUnitary
        theta hCAR hHermitian J hJ).symm p.2) ∈
      (independentActualE2NativeHilbertChargeColumn
        theta hCAR hHermitian color gamma).graph := by
  let U := independentPhysicalUnitary theta hCAR hHermitian J hJ
  let V := independentPhysicalHilbertOutputUnitary
    theta hCAR hHermitian J hJ
  refine FCP.M4F9H4C2A1GenericPartialGraphReverse.partialGraph_reverse_of_domain_forward
    (independentActualE2NativeHilbertChargeColumn
      theta hCAR hHermitian color gamma)
    pairedOriginalNativePhysicalHilbertChargeColumn
    U U.symm V V.symm
    (fun x => U.apply_symm_apply x)
    (fun y => V.symm_apply_apply y)
    ?_ ?_ p hp
  · intro x hx
    exact FCP.M4F9H4C1BSourceDomainIndependentNativeRecovery.nativeSourceDomain_symm_mem_independentDomain
      theta hCAR hHermitian color gamma J hColor hGamma hJ x hx
  · intro x y hxy
    exact FCP.M4F9H4B1CNativeSourceGraphForward.nativeIndependentGraph_mem_sourceGraph
      theta hCAR hHermitian color gamma J hColor hGamma hJ (x,y) hxy

#print axioms nativeSourceGraph_mem_independentGraph
end
end FCP.M4F9H4C2A2ActualNativeReverseFromGeneric
