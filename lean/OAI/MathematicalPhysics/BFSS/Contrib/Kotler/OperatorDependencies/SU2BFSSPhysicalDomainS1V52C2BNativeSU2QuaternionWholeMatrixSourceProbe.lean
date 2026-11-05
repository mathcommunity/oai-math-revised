import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52C2ANativeSU2MatrixAdjugateSourceProbe

/-!
S1V52-C2B research candidate: exact whole-matrix reconstruction of
the genuine native OAI.BFSSQuantum.GaugeGroup 2 from upper-row complex
coordinates. This copies the *mathematical form and proof pattern* of
the previously strictly qualified L6H5E8Q source theorem, using the
narrow C2A adjugate and row-sign interface instead of importing the
entire historical L6H5E8P/Q chain.

C2A is a candidate until its exact source-hash strict Gate #1 succeeds.
No mathematical result is promoted from this file before independent CI.

This is not yet the real-coordinate polynomial-to-GaugeGroup matrix
equality, not native quaternion multiplication, and NOT Spin membership.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000

namespace FCP.BFSSS1V52C2B
noncomputable section
open OAI.BFSSQuantum
open Matrix
open FCP.BFSSS1V52C2A

/-- The original SU2 group element is exactly determined, including
the source signs, by its upper-row complex entries. -/
theorem originalNativeSU2_wholeQuaternionMatrix
    (g : GaugeGroup 2) :
    (g : ColorMatrix 2) =
      !![(g : ColorMatrix 2) 0 0, (g : ColorMatrix 2) 0 1;
         -star ((g : ColorMatrix 2) 0 1),
         star ((g : ColorMatrix 2) 0 0)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [originalNativeSU2_bottomRight_eq_conj_topLeft,
      originalNativeSU2_bottomLeft_eq_neg_conj_topRight]

#print axioms originalNativeSU2_wholeQuaternionMatrix

end
end FCP.BFSSS1V52C2B
