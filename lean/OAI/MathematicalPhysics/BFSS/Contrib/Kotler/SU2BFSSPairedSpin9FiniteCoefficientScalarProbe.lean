import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9FiniteCoefficientLiftProbe

/-!
K1D18V8Y — scalar homogeneity of the source-exact finite 9-to-48
candidate coefficient lift, with native SpaceIndex input and paired
Source48Label output. Accepted V8X proved rho(0) and rho(A+B).

This stage tests rho(c • A) = c • rho(A) for every real scalar c
and every real 9×9 input matrix A. It is a scalar law for the
candidate, not yet a constructed LinearMap on skew carriers or an
arbitrary Lie-bracket preservation theorem.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open scoped BigOperators

/-- Real scalar homogeneity of the exact native nine-index coefficient
lift to original 48-real paired-Fock matrices. -/
theorem coordinateToPairedFiniteLift_smul
    (c : ℝ) (A : Matrix SpaceIndex SpaceIndex ℝ) :
    coordinateToPairedFiniteLift (c • A) =
      c • coordinateToPairedFiniteLift A := by
  simp only [coordinateToPairedFiniteLift, Matrix.smul_apply,
    Finset.smul_sum, smul_smul, smul_eq_mul]
  -- The only remaining difference is the order of real scalar factors.
  -- Prove it pointwise; do not globally permute rewrite rules under sums.
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  exact congrArg (fun z : ℝ => z • normalizedPairedPlane r s)
    (show (1 / 2 : ℝ) * (c * A r s) =
      c * ((1 / 2 : ℝ) * A r s) by ring)

#print axioms coordinateToPairedFiniteLift_smul

end
end FCP.BFSSPairedSpin9Plane
