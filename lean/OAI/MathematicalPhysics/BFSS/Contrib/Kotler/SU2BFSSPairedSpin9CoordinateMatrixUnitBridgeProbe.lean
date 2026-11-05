import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9CoordinatePlaneCarrierProbe
import Mathlib.Data.Matrix.Basis

/-!
K1D18V8T — source-native 9×9 input coordinate plane to Mathlib's
pinned, typed matrix units (Matrix.single).

The input F_rs := E_rs - E_sr is proved equal to the difference of
literal Mathlib single-entry 9×9 matrices on exact SpaceIndex.

This step does not infer a matrix-unit product, full so(9) bracket,
linear extension to the 48-real original paired generator family,
Lie algebra homomorphism or global Spin(9) group lift.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum

/-- The original 9×9 coordinate plane is exactly the difference of
pinned Mathlib's matrix units on native SpaceIndex. -/
theorem coordinatePlane9_eq_single_sub_single (r s : SpaceIndex) :
    coordinatePlane9 r s =
      (Matrix.single r s (1 : ℝ) : Matrix SpaceIndex SpaceIndex ℝ) -
        Matrix.single s r (1 : ℝ) := by
  ext i j
  change
    ((if i = r ∧ j = s then (1 : ℝ) else 0) -
      (if i = s ∧ j = r then (1 : ℝ) else 0)) =
    ((if r = i ∧ s = j then (1 : ℝ) else 0) -
      (if s = i ∧ r = j then (1 : ℝ) else 0))
  simp only [eq_comm]

#print axioms coordinatePlane9_eq_single_sub_single

end
end FCP.BFSSPairedSpin9Plane
