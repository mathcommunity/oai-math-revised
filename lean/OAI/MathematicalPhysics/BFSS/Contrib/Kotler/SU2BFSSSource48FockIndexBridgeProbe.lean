import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V7OriginalSourceSixteenBlockLabelBridgeProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2PairedThetaConcreteModesProbe

/-!
Exact original 48-real Source48 label to actual Fock Majorana *index*
identification. This proves a statement about the same explicitly indexed
24-mode fermion operators, not an intertwiner of Clifford representations.
Its two parents must independently qualify before this probe is admitted.
-/

set_option autoImplicit false

namespace FCP.BFSSSource48FockIndexBridge
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSFermionF2
open FCP.BFSSS1V5
open FCP.BFSSS1V7
open FCP.BFSSPairedThetaLabelCrosswalk

theorem sourceBlockColorMajorana_eq_G1APairedTheta
    (j : Fin 8) (s : Fin 2) (A : ColorIndex 2) :
    majoranaCandidate (sourceBlockColorLabel (j, s) A) =
      pairedTheta (spinPairEquiv.symm (j, s)) A := by
  rw [sourceBlockColorLabel_eq_original_paired]
  rfl

#print axioms sourceBlockColorMajorana_eq_G1APairedTheta

end
end FCP.BFSSSource48FockIndexBridge
