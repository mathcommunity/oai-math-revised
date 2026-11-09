import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9CoordinateMatrixUnitBridgeProbe

/-!
K1D18V8U — exact native 9×9 matrix-unit multiplication on SpaceIndex.

The source-pinned Mathlib matrix-unit identities
Matrix.single_mul_single_same and Matrix.single_mul_single_of_ne
distinguish matching/mismatching inner spatial labels. Prove the
single typed delta-conditional formula for ALL four spatial indices.

No 9-to-48 linear map, so(9) bracket or group integration is claimed.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum

/-- Exact multiplication table for native nine-index real matrix units,
including the inner-index coincidence and mismatch cases. -/
theorem coordinateMatrixUnit9_mul (r s t u : SpaceIndex) :
    (Matrix.single r s (1 : ℝ) : Matrix SpaceIndex SpaceIndex ℝ) *
      Matrix.single t u (1 : ℝ) =
    if s = t then (Matrix.single r u (1 : ℝ) : Matrix SpaceIndex SpaceIndex ℝ)
    else 0 := by
  by_cases hst : s = t
  · subst t
    simp
  · have hzero :
        (Matrix.single r s (1 : ℝ) : Matrix SpaceIndex SpaceIndex ℝ) *
          Matrix.single t u (1 : ℝ) = 0 :=
      Matrix.single_mul_single_of_ne (c := (1 : ℝ)) r s t hst (1 : ℝ)
    simp only [hst, ite_false]
    exact hzero

#print axioms coordinateMatrixUnit9_mul

end
end FCP.BFSSPairedSpin9Plane
