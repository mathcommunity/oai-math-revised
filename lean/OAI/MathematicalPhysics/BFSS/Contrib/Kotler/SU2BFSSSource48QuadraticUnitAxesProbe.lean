import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V5ConcreteSixteenSourceColorBlocksProbe
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Original positive Source48 quadratic form on actual source coordinate axes

This is independent of the Fock gamma construction. The original
source48Quadratic is the unit-weight sum of squares on precisely
Source48Label = Fin 24 × Fin 2. We certify that each actual
S1V5 block/color coordinate axis has quadratic value one.

It supplies the source-side normalization obligation for a future
Clifford universal homomorphism; it does not prove its existence.
-/

set_option autoImplicit false
set_option maxHeartbeats 280000

namespace FCP.BFSSSource48QuadraticUnitAxes
noncomputable section

open Matrix
open FCP.BFSSS1V0
open FCP.BFSSS1V5

/-- Exact unit-weight original Source48 quadratic form is the
usual dot product, with no alternative or rescaled quadratic form. -/
theorem source48Quadratic_eq_dot (v : Source48Vector) :
    source48Quadratic v = dotProduct v v := by
  simp [source48Quadratic, QuadraticMap.weightedSumSquares_apply,
    dotProduct]

/-- Every actual block/color coordinate axis has positive Clifford
quadratic norm one, matching the required normalized Fock gamma square. -/
theorem sourceBlockColorAxis_quadratic_one
    (j : Fin 8) (s : Fin 2) (A : ColorLabel) :
    source48Quadratic (sourceBlockColorAxis (j, s) A) = 1 := by
  rw [source48Quadratic_eq_dot]
  change (∑ p : Source48Label,
    sourceBlockColorAxis (j, s) A p *
      sourceBlockColorAxis (j, s) A p) = 1
  rw [Finset.sum_eq_single (sourceBlockColorLabel (j, s) A)]
  · rw [sourceBlockColorAxis_self]
    norm_num
  · intro p hp hneq
    have hzero : sourceBlockColorAxis (j, s) A p = 0 := by
      simp [sourceBlockColorAxis, hneq]
    simp only [hzero, mul_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

#print axioms source48Quadratic_eq_dot
#print axioms sourceBlockColorAxis_quadratic_one

end
end FCP.BFSSSource48QuadraticUnitAxes
