import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2PairedThetaLabelCrosswalkProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V5ConcreteSixteenSourceColorBlocksProbe

/-!
S1V7 — exact original normalized Pauli source majorana label bridge.

The accepted original G1A supplies:
* SpinIndex = Fin 16 and spinPairEquiv to Fin 8 × Fin 2;
* ColorIndex 2 = Fin 3 and colorModeEquiv = finProdFinEquiv;
* pairedLabelEquiv original (SpinIndex × ColorIndex 2) ≃
  (Fin 24 × Fin 2).

The standalone S1V5 gate constructs its own equivalent 16 × 3
ordering using precisely that finProdFinEquiv expression.

This file states literal equality of the original and standalone
color mode packing and the paired original Majorana label at arbitrary
spin-block and color. It is a source interoperability CANDIDATE
until ORIGINAL G1A import closure has a strict kernel CI qualification.

No continuous SU2→Spin48, original Fock intertwiner, or spectral theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 280000

namespace FCP.BFSSS1V7
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSPairedThetaLabelCrosswalk
open FCP.BFSSS1V5

theorem sourceColorModeEquiv_eq_original :
    sourceColorModeEquiv = colorModeEquiv := rfl

/-- The exact original source paired-label equivalence takes
a real-spin block and color to the source-sized standalone label. -/
theorem sourceBlockColorLabel_eq_original_paired
    (j : Fin 8) (s : Fin 2) (A : ColorIndex 2) :
    sourceBlockColorLabel (j, s) A =
      pairedLabelEquiv (spinPairEquiv.symm (j, s), A) := by
  simp only [sourceBlockColorLabel, sourceBlockColorEquiv,
    pairedLabelEquiv, Equiv.coe_fn_mk]
  rw [Equiv.apply_symm_apply]
  rfl

#print axioms sourceColorModeEquiv_eq_original
#print axioms sourceBlockColorLabel_eq_original_paired

end
end FCP.BFSSS1V7
