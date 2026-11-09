import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V5ConcreteSixteenSourceColorBlocksProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG1APairedThetaProbe

/-!
S1V52L9D0 — STAGED, UNQUALIFIED original BFSS Fock/Spin48
Majorana LABEL equality. This is the concrete source-label bridge
independent of source color-adjoint and Spin48 conjugation.

S1V5.sourceBlockColorLabel encodes RealSpinBlock=(Fin8×Fin2),
A=(Fin3), with original sourceColorModeEquiv=finProdFinEquiv.
G1A.pairedLabelEquiv encodes original SpinIndex and ColorIndex2
through spinPairEquiv and colorModeEquiv=finProdFinEquiv. This
theorem identifies these literal index packings in the original
Fin24×Fin2 source space, without hypothesizing a new index map.

STAGED ONLY: this source-label statement remains unqualified until
its own strict source-pinned CI and axiom validator. Original
48-dimensional Spin projection and physical spectral claims remain
distinct unproved obligations.
-/

set_option autoImplicit false
set_option maxHeartbeats 260000

namespace FCP.BFSSS1V52L9D0
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V5
open FCP.BFSSSU2GaugeG1A

/-- The original 48-real source axis coordinate and the actual
BFSS paired Fock Majorana coordinate refer to the SAME index. -/
theorem originalSourceBlockColorLabel_eq_originalPairedLabel
    (α : RealSpinBlock) (A : Fin 3) :
    sourceBlockColorLabel α A =
      pairedLabelEquiv (spinPairEquiv.symm α, A) := by
  rcases α with ⟨j,s⟩
  simp [sourceBlockColorLabel, sourceBlockColorEquiv,
    pairedLabelEquiv, sourceColorModeEquiv, colorModeEquiv]

#print axioms originalSourceBlockColorLabel_eq_originalPairedLabel

end
end FCP.BFSSS1V52L9D0
