import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1JActual48RealMajoranaColorActionProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9D0ActualFockSpinBlockSourceLabelEqualityProbe

/-!
S1V52L9D7 — STAGED, UNQUALIFIED: the exact original Fock
48-real Majorana gauge matrix has native BFSS adjointColorMatrix
coefficients on the original 16-by-3 source-block paired labels.

Original sourceRealMajoranaMatrix is the REAL Fock source matrix
R24(g) ⊗ I2 on the SAME Fin24×Fin2 source labels as S1V5. The
source real/imaginary Majorana bit remains unchanged. The original
G3B oneParticleMatrix_block formula fixes output B/input A order.

One candidate theorem; no strict gate yet. This is SOURCE MATRIX
ENTRY equality, not 48-vector mulVec, global Spin48 projection,
concrete Fock implementing unitary, continuity, Hamiltonian or gap.

Independent of unqualified L9D5/L9D6 ordered Spin48 proofs.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000

namespace FCP.BFSSS1V52L9D7
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V5
open FCP.BFSSS1V52L9D0
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG3A
open FCP.BFSSSU2GaugeG3B
open FCP.BFSSSU2PhysicalDomainS1J

/-- Original 48-real Fock Majorana matrix entry is exactly
the native BFSS adjoint-color coefficient within the SAME source
real spin block and zero between different real blocks. -/
theorem originalSourceRealMajoranaMatrix_sourceBlock_entry
    (g : GaugeGroup 2)
    (α β : RealSpinBlock) (A B : Fin 3) :
    sourceRealMajoranaMatrix g
      (sourceBlockColorLabel β B)
      (sourceBlockColorLabel α A) =
    if β = α then adjointColorMatrix g B A else 0 := by
  rcases α with ⟨j,s⟩
  rcases β with ⟨k,t⟩
  change
    sourceRealMajoranaMatrix g
      (colorModeEquiv (k,B),t)
      (colorModeEquiv (j,A),s) =
    if (k,t) = (j,s) then adjointColorMatrix g B A else 0
  rw [sourceRealMajoranaMatrix_entry]
  rw [oneParticleMatrix_block]
  by_cases hjk : k = j <;> by_cases hts : t = s <;>
    simp [hjk, hts, Prod.mk.injEq]

#print axioms originalSourceRealMajoranaMatrix_sourceBlock_entry

end
end FCP.BFSSS1V52L9D7
