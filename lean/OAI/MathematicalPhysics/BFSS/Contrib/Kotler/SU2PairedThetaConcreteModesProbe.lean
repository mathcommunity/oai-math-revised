import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2PairedThetaLabelCrosswalkProbe

/-!
# G1A pairedTheta even/odd source-mode selection

These four theorem statements and proof routes follow the original G1A
SU2BFSSG1APairedThetaProbe.lean source at blob
4f8fbf05a35c1d625746931b7ff0361b7ffc2ec4.
Unlike the older generic Fintype.equivFin indexing, the exact G1A pair
assignment places the even and odd spin components at the *same*
24-mode complex Fock coordinate. It identifies source modes only,
not global gauge/Spin actions or any spectral existence.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedThetaConcreteModes
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSFermionF1 FCP.BFSSFermionF2
open FCP.BFSSPairedThetaLabelCrosswalk

theorem pairedLabel_even (j : Fin 8) (A : ColorIndex 2) :
    pairedLabelEquiv (spinPairEquiv.symm (j, (0 : Fin 2)), A) =
      (colorModeEquiv (j, A), (0 : Fin 2)) := by
  simp [pairedLabelEquiv]

theorem pairedLabel_odd (j : Fin 8) (A : ColorIndex 2) :
    pairedLabelEquiv (spinPairEquiv.symm (j, (1 : Fin 2)), A) =
      (colorModeEquiv (j, A), (1 : Fin 2)) := by
  simp [pairedLabelEquiv]

theorem pairedTheta_even (j : Fin 8) (A : ColorIndex 2) :
    pairedTheta (spinPairEquiv.symm (j, (0 : Fin 2))) A =
      majorana0 (colorModeEquiv (j, A)) := by
  rw [pairedTheta, pairedLabel_even]
  simp [majoranaCandidate]

theorem pairedTheta_odd (j : Fin 8) (A : ColorIndex 2) :
    pairedTheta (spinPairEquiv.symm (j, (1 : Fin 2))) A =
      majorana1 (colorModeEquiv (j, A)) := by
  rw [pairedTheta, pairedLabel_odd]
  simp [majoranaCandidate]

#print axioms pairedLabel_even
#print axioms pairedLabel_odd
#print axioms pairedTheta_even
#print axioms pairedTheta_odd

end
end FCP.BFSSPairedThetaConcreteModes

/-!
Independent BFSS source-label bridge for etblink/math.
Source formula provenance: FCP/G1A, Git blob
4f8fbf05a35c1d625746931b7ff0361b7ffc2ec4.
Copyright (c) 2026 Evan T. Kotler. SPDX-License-Identifier: Apache-2.0.
No upstream mathcommunity PR authorized.
-/
