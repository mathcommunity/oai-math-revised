import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9AdjacentLieBracketProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9OrientationSwapProbe

/-!
K1D18V8F — shared-left Spin(9) bracket on the original paired 48-Fock labels.

This is the exact companion to V8E, not an alternate or color-major
construction. The accepted V8B original 48-label adjacent-plane bracket
and V8D original 48-label orientation reversal imply
[K(r,s), K(r,t)] = +2 K(s,t) for three pairwise distinct spatial labels.
No group lift, exact B-field covariance, or physical BFSS result claimed.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum

/-- Source-exact doubled generator bracket with a shared LEFT spatial label. -/
theorem originalPairedPlane_shared_left_bracket
    (r s t : SpaceIndex) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    originalPairedPlane r s * originalPairedPlane r t -
        originalPairedPlane r t * originalPairedPlane r s =
      originalPairedPlane s t + originalPairedPlane s t := by
  have h := originalPairedPlane_adjacent_bracket
    s r t (Ne.symm hrs) hrt hst
  rw [originalPairedPlane_swap_order r s hrs] at h
  calc
    originalPairedPlane r s * originalPairedPlane r t -
        originalPairedPlane r t * originalPairedPlane r s =
      -((-originalPairedPlane r s) * originalPairedPlane r t -
        originalPairedPlane r t * (-originalPairedPlane r s)) := by
        simp only [neg_mul, mul_neg]
        abel
    _ = -(-(originalPairedPlane s t + originalPairedPlane s t)) := by
      rw [h]
    _ = originalPairedPlane s t + originalPairedPlane s t := neg_neg _

#print axioms originalPairedPlane_shared_left_bracket

end
end FCP.BFSSPairedSpin9Plane
