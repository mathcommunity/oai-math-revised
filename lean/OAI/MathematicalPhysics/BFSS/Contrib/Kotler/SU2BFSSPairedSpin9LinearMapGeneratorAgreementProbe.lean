import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9LinearMapMatrixUnitEvaluationProbe

/-!
K1D18V9B — source-native normalized plane generator agreement.

Use the strict accepted V9A matrix-unit evaluation with the
original native 9-index source identity F_rs = E_rs - E_sr and
the accepted original paired 48-real H_sr = -H_rs.

Result: rho(F_rs) = H_rs for every spatial pair, including
r=s; no external pairwise-distinctness or basis permutation.

This matches generators only. Arbitrary skew-carrier spanning
and Lie bracket preservation still require separate proofs;
no group or physical claim follows from this theorem alone.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0

/-- Source-exact generator agreement between the native so(9)
coordinate-plane matrices and normalized original paired-Fock
48-real generators, without restrictions on index coincidences. -/
theorem coordinateToPairedLinearMap_coordinatePlane
    (r s : SpaceIndex) :
    coordinateToPairedLinearMap (coordinatePlane9 r s) =
      normalizedPairedPlane r s := by
  calc
    coordinateToPairedLinearMap (coordinatePlane9 r s) =
        (1 / 2 : ℝ) • normalizedPairedPlane r s -
        (1 / 2 : ℝ) • normalizedPairedPlane s r := by
      rw [coordinatePlane9_eq_single_sub_single r s,
        map_sub,
        coordinateToPairedLinearMap_matrixUnit r s,
        coordinateToPairedLinearMap_matrixUnit s r]
    _ = normalizedPairedPlane r s := by
      rw [normalizedPairedPlane_swap r s, smul_neg, sub_neg_eq_add, ← add_smul]
      rw [show (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 by norm_num, one_smul]

#print axioms coordinateToPairedLinearMap_coordinatePlane

end
end FCP.BFSSPairedSpin9Plane
