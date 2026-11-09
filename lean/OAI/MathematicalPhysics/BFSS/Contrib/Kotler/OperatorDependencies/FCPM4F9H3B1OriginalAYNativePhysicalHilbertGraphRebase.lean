import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H3AOriginalPairedPhysicalChargeOutputConstraint

/-!
BFSS M4F9 H3B1 — ORIGINAL AY paired source charge graph, rebased to
genuine physical sixteen-output PiLp 2 Hilbert coordinates.

This first stage constructs the literal physical-output-to-original-
ambient-output coordinate inclusion, proves its injectivity and pulls
back the ACTUAL AY charge's graph. No new gauge source, charge,
artificial extension, unproved domain, adjoint or Hamiltonian identity.
The original physical output space is a PROPER subspace of ambient
FullL2 in general; no false onto-ambient assertion.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H3B1OriginalAYNativePhysicalHilbertGraphRebase
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6H5E8AY
open MeasureTheory Set

/-- True linear coordinate embedding of original paired gauge-physical
Hilbert sixteen-output direct sum into the original AY FULL L² output
direct sum. It is NOT onto the ambient FullL2 sixteen-output space. -/
noncomputable def pairedPhysicalHilbertOutputsToOriginalAmbient :
    PiLp 2 (fun _ : SpinIndex => pairedGaugeData.physicalSpace) →ₗ[ℂ]
      PiLp 2 (fun _ : SpinIndex => FullL2 2) where
  toFun v := WithLp.toLp 2 (fun α : SpinIndex =>
    ((v α : pairedGaugeData.physicalSpace) : FullL2 2))
  map_add' := by
    intro v w
    apply PiLp.ext
    intro α
    rfl
  map_smul' := by
    intro c v
    apply PiLp.ext
    intro α
    rfl

/-- The true original output embedding preserves each actual output
coordinate literally, with no normalization or index permutation. -/
theorem pairedPhysicalHilbertOutputsToOriginalAmbient_apply
    (v : PiLp 2 (fun _ : SpinIndex => pairedGaugeData.physicalSpace))
    (α : SpinIndex) :
    pairedPhysicalHilbertOutputsToOriginalAmbient v α =
      (v α : FullL2 2) := by
  rfl

/-- In particular the original physical sixteen-charge outputs retain
all the information when embedded in the AY ambient Hilbert codomain. -/
theorem pairedPhysicalHilbertOutputsToOriginalAmbient_injective :
    Function.Injective pairedPhysicalHilbertOutputsToOriginalAmbient := by
  intro a b hab
  apply PiLp.ext
  intro α
  apply Subtype.ext
  exact congrArg
    (fun w : PiLp 2 (fun _ : SpinIndex => FullL2 2) => w α) hab

/-- The actual AY minimal source charge graph, not a redefined charge,
pulled back along the literal original source gauge-physical output
inclusion into the original ambient AY sixteen-output Hilbert space. -/
noncomputable def pairedOriginalPhysicalHilbertChargeGraph :
    Submodule ℂ (pairedGaugeData.physicalSpace ×
      PiLp 2 (fun _ : SpinIndex => pairedGaugeData.physicalSpace)) :=
  ((originalMinimalPhysicalHilbertChargeColumn
    pairedAlgebraData pairedGaugeData).graph).comap
    ((LinearMap.id : pairedGaugeData.physicalSpace →ₗ[ℂ]
      pairedGaugeData.physicalSpace).prodMap
      pairedPhysicalHilbertOutputsToOriginalAmbient)

/-- The H3B1 physical-output graph is EXACTLY the preimage of the
original AY graph, including original physical input subtype. -/
theorem pairedOriginalPhysicalHilbertChargeGraph_mem_iff
    (p : pairedGaugeData.physicalSpace ×
      PiLp 2 (fun _ : SpinIndex => pairedGaugeData.physicalSpace)) :
    p ∈ pairedOriginalPhysicalHilbertChargeGraph ↔
      (p.1, pairedPhysicalHilbertOutputsToOriginalAmbient p.2) ∈
        (originalMinimalPhysicalHilbertChargeColumn
          pairedAlgebraData pairedGaugeData).graph := by
  rfl

#print axioms pairedPhysicalHilbertOutputsToOriginalAmbient
#print axioms pairedPhysicalHilbertOutputsToOriginalAmbient_apply
#print axioms pairedPhysicalHilbertOutputsToOriginalAmbient_injective
#print axioms pairedOriginalPhysicalHilbertChargeGraph
#print axioms pairedOriginalPhysicalHilbertChargeGraph_mem_iff

end
end FCP.M4F9H3B1OriginalAYNativePhysicalHilbertGraphRebase
