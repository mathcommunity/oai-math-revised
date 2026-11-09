import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9InputSkewMatrixUnitBridgeProbe

/-!
K1D18V9E — source-native antisymmetric-part coefficient identity,
with no skew hypothesis yet.

For every real 9×9 matrix A, the sum of coefficients A_rs
against exact coordinate planes F_rs = E_rs - E_sr equals
A - A.transpose. This proves an ordered-pair matrix identity
on the original SpaceIndex carrier and preserves all pair
coincidences.

A = 1/2 • sum A_rs • F_rs for skew A will be a separate V9F
consequence. Full arbitrary skew Lie bracket preservation, global
Spin(9) integration, and BFSS physics are still open.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open scoped BigOperators

/-- The full native coordinate-plane coefficient sum is the
antisymmetric part of any real 9×9 source matrix. -/
theorem coordinateMatrix9_antisymmetric_part_expansion
    (A : Matrix SpaceIndex SpaceIndex ℝ) :
    (∑ r : SpaceIndex, ∑ s : SpaceIndex,
       (A r s) • coordinatePlane9 r s) = A - A.transpose := by
  let E (r s : SpaceIndex) : Matrix SpaceIndex SpaceIndex ℝ :=
    Matrix.single r s (1 : ℝ)
  have hunit : A =
      ∑ r : SpaceIndex, ∑ s : SpaceIndex, (A r s) • E r s :=
    coordinateMatrix9_coefficients_on_units A
  have hflip :
      (∑ r : SpaceIndex, ∑ s : SpaceIndex, (A r s) • E s r) =
        A.transpose := by
    calc
      (∑ r : SpaceIndex, ∑ s : SpaceIndex, (A r s) • E s r) =
          (∑ r : SpaceIndex, ∑ s : SpaceIndex, (A r s) • E r s).transpose := by
        simp only [E, Matrix.transpose_sum, Matrix.transpose_smul,
          Matrix.transpose_single]
      _ = A.transpose := congrArg Matrix.transpose hunit.symm
  calc
    (∑ r : SpaceIndex, ∑ s : SpaceIndex,
        (A r s) • coordinatePlane9 r s) =
      ∑ r : SpaceIndex, ∑ s : SpaceIndex,
        ((A r s) • E r s - (A r s) • E s r) := by
          apply Finset.sum_congr rfl
          intro r hr
          apply Finset.sum_congr rfl
          intro s hs
          rw [coordinatePlane9_eq_single_sub_single r s, smul_sub]
    _ = (∑ r : SpaceIndex, ∑ s : SpaceIndex, (A r s) • E r s) -
        (∑ r : SpaceIndex, ∑ s : SpaceIndex, (A r s) • E s r) := by
          simp only [Finset.sum_sub_distrib]
    _ = A - A.transpose := congrArg₂ (· - ·) hunit.symm hflip

#print axioms coordinateMatrix9_antisymmetric_part_expansion

end
end FCP.BFSSPairedSpin9Plane
