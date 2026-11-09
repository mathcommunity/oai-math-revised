import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4D4BActualNativeAdjointSquareAction

/-!
BFSS M4F9 H4E1A — Original AY native physical-output to ambient
FullL2 sixteen-output Hilbert inner-product bridge.

The actual H3B1 source-defined coordinate embedding is linear/injective.
Here verify its exact Hilbert pairing, *without* treating the
physical-output inclusion as surjective onto ambient FullL2.
This is a prerequisite for comparing genuine adjoints and
the historical original normalized ambient-output Hamiltonian.
No Hamiltonian, adjoint domain, or spectrum assertion yet.
-/
set_option autoImplicit false
set_option maxHeartbeats 240000

namespace FCP.M4F9H4E1AOriginalAmbientOutputInnerBridge
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.M4F9H3B1OriginalAYNativePhysicalHilbertGraphRebase
open MeasureTheory Set

/-- Exact Hilbert inner pairing of the ACTUAL source AY sixteen-output
physical→ambient coordinate map. No false onto-ambient unitary. -/
theorem pairedPhysicalHilbertOutputsToOriginalAmbient_inner
    (v w : PiLp 2 (fun _ : SpinIndex => pairedGaugeData.physicalSpace)) :
    inner ℂ (pairedPhysicalHilbertOutputsToOriginalAmbient v)
      (pairedPhysicalHilbertOutputsToOriginalAmbient w) =
    inner ℂ v w := by
  simp only [PiLp.inner_apply,
    pairedPhysicalHilbertOutputsToOriginalAmbient_apply]
  rfl

#print axioms pairedPhysicalHilbertOutputsToOriginalAmbient_inner
end
end FCP.M4F9H4E1AOriginalAmbientOutputInnerBridge
