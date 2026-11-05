import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9NormalizedPlaneInterfaceProbe

/-!
K1D18V8P — exact original-paired 48-real *normalized* adjacent
Spin(9) commutator. The source-defined H_rs=-(1/2) • L_rs gives the
standard positive structure coefficient on adjacent oriented planes.

This is a bounded sign and typed scalar bridge only. It does not
establish a linear extension, all-four-index normalized bracket, a
Spin(9) group integration, or any physical BFSS claim.

The proof reuses the accepted V8I original-label L adjacent bracket
with Mathlib's typed matrix scalar-multiplication identities. No
unproved source-basis identification, axioms or proof limits.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum

/-- The genuine normalized source-native plane matrices satisfy the
standard positive adjacent so(9) commutator coefficient. -/
theorem normalizedPairedPlane_adjacent_bracket
    (r s t : SpaceIndex) (hrs : r ≠ s) (hst : s ≠ t) (hrt : r ≠ t) :
    normalizedPairedPlane r s * normalizedPairedPlane s t -
      normalizedPairedPlane s t * normalizedPairedPlane r s =
    normalizedPairedPlane r t := by
  unfold normalizedPairedPlane
  calc
    ((-(1 / 2 : ℝ)) • zeroDiagonalPairedPlane r s) *
        ((-(1 / 2 : ℝ)) • zeroDiagonalPairedPlane s t) -
        ((-(1 / 2 : ℝ)) • zeroDiagonalPairedPlane s t) *
          ((-(1 / 2 : ℝ)) • zeroDiagonalPairedPlane r s) =
      ((-(1 / 2 : ℝ)) * (-(1 / 2 : ℝ))) •
        (zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane s t -
          zeroDiagonalPairedPlane s t * zeroDiagonalPairedPlane r s) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_sub]
    _ = ((-(1 / 2 : ℝ)) * (-(1 / 2 : ℝ))) •
          (-(zeroDiagonalPairedPlane r t + zeroDiagonalPairedPlane r t)) := by
      rw [zeroDiagonalPairedPlane_adjacent_bracket r s t hrs hst hrt]
    _ = (-(1 / 2 : ℝ)) • zeroDiagonalPairedPlane r t := by
      ext i j
      simp only [Matrix.smul_apply, Matrix.neg_apply, Matrix.add_apply, smul_eq_mul]
      ring

#print axioms normalizedPairedPlane_adjacent_bracket

end
end FCP.BFSSPairedSpin9Plane
