import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9AdjacentLieBracketProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9OrientationSwapProbe

/-!
K1D18V8E — exact native paired-Fock shared-right-end Spin(9) bracket.

The accepted V8B adjacent-plane Lie bracket and accepted V8D orientation
reversal imply [K(r,s), K(t,s)] = +2 K(r,t), for three pairwise distinct
original spatial indices. Uses the SAME literal original Source48Label
matrices. This is not a global so(9) Lie representation or Spin(9) lift.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum

/-- Companion to the accepted adjacent-plane bracket: when both planes
have the same right endpoint, the doubled-generator bracket has +2 sign. -/
theorem originalPairedPlane_shared_right_bracket
    (r s t : SpaceIndex) (hrs : r ≠ s) (hst : s ≠ t) (hrt : r ≠ t) :
    originalPairedPlane r s * originalPairedPlane t s -
      originalPairedPlane t s * originalPairedPlane r s =
    originalPairedPlane r t + originalPairedPlane r t := by
  rw [originalPairedPlane_swap_order s t hst]
  calc
    originalPairedPlane r s * (-originalPairedPlane s t) -
        (-originalPairedPlane s t) * originalPairedPlane r s =
      -(originalPairedPlane r s * originalPairedPlane s t -
        originalPairedPlane s t * originalPairedPlane r s) := by
        simp only [mul_neg, neg_mul]
        abel
    _ = -( -(originalPairedPlane r t + originalPairedPlane r t)) := by
        rw [originalPairedPlane_adjacent_bracket r s t hrs hst hrt]
    _ = originalPairedPlane r t + originalPairedPlane r t := neg_neg _

#print axioms originalPairedPlane_shared_right_bracket

end
end FCP.BFSSPairedSpin9Plane
