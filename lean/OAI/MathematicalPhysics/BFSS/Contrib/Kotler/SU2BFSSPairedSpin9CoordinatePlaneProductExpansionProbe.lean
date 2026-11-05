import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9CoordinateMatrixUnitProductProbe

/-!
K1D18V8V — source-native 9×9 coordinate-plane product, expressed
using the pinned Matrix.single algebra and all four conditional
matrix-unit terms, with no pairwise-distinctness restriction.

This is a single typed input product expansion, NOT the full
input so(9) commutator, a linear 9×9 → 48×48 representation or
a global Spin(9) group lift. No assumptions or proof limits added.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum

/-- The complete 9×9 matrix-unit product expansion of
F_rs F_tu, including every coincidence of spatial indices. -/
theorem coordinatePlane9_mul_expanded (r s t u : SpaceIndex) :
    coordinatePlane9 r s * coordinatePlane9 t u =
      ((if s = t then
          (Matrix.single r u (1 : ℝ) : Matrix SpaceIndex SpaceIndex ℝ)
        else 0) -
       (if r = t then
          (Matrix.single s u (1 : ℝ) : Matrix SpaceIndex SpaceIndex ℝ)
        else 0)) -
      ((if s = u then
          (Matrix.single r t (1 : ℝ) : Matrix SpaceIndex SpaceIndex ℝ)
        else 0) -
       (if r = u then
          (Matrix.single s t (1 : ℝ) : Matrix SpaceIndex SpaceIndex ℝ)
        else 0)) := by
  rw [coordinatePlane9_eq_single_sub_single r s,
      coordinatePlane9_eq_single_sub_single t u]
  simp only [sub_mul, mul_sub, coordinateMatrixUnit9_mul]

#print axioms coordinatePlane9_mul_expanded

end
end FCP.BFSSPairedSpin9Plane
