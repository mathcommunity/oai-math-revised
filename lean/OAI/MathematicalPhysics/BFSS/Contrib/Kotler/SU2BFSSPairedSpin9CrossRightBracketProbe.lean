import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9SharedLeftBracketProbe

/-!
K1D18V8G — fourth shared-index orientation, on the actual original
paired-Fock 48-real Spin(9) generator matrices.

For pairwise distinct spatial indices:
  [K(r,s), K(t,r)] = -2 K(s,t).
Derives directly from strictly accepted V8F shared-left bracket and
V8D orientation reversal. This has the exact original Source48Label
without replacing its paired ordering with color-major indexing.

It does NOT establish a blanket so(9) bracket on diagonal raw K(r,r)
(which equals -I), group integration, Fock implementation, or physics.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum

/-- The fourth pairwise-distinct shared-index orientation, normalized for
the actual doubled plane matrices K on the native source 48 labels. -/
theorem originalPairedPlane_cross_right_bracket
    (r s t : SpaceIndex) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    originalPairedPlane r s * originalPairedPlane t r -
        originalPairedPlane t r * originalPairedPlane r s =
      -(originalPairedPlane s t + originalPairedPlane s t) := by
  rw [originalPairedPlane_swap_order r t hrt]
  calc
    originalPairedPlane r s * (-originalPairedPlane r t) -
        (-originalPairedPlane r t) * originalPairedPlane r s =
      -(originalPairedPlane r s * originalPairedPlane r t -
        originalPairedPlane r t * originalPairedPlane r s) := by
        simp only [mul_neg, neg_mul]
        abel
    _ = -(originalPairedPlane s t + originalPairedPlane s t) := by
        rw [originalPairedPlane_shared_left_bracket r s t hrs hrt hst]

#print axioms originalPairedPlane_cross_right_bracket

end
end FCP.BFSSPairedSpin9Plane
