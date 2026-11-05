import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9OrthogonalExponentialProbe
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
K1D18V9V — true orthogonal-group membership for exponentials of the
exact original Fock-paired 48-real skew matrices.

V9U establishes the transpose/inverse identity. Pinned Mathlib's
Matrix.isUnit_exp and Matrix.mem_orthogonalGroup_iff identify these
individual exponentials as actual members of Matrix.orthogonalGroup.

This does not prove det = 1, membership in specialOrthogonalGroup,
a global continuous Spin(9) to SO(48) homomorphism, or a Spin(48) lift.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open NormedSpace

/-- For an arbitrary source-exact paired-Fock skew matrix, every real
parameter exponentiates into Mathlib's actual orthogonal group. -/
theorem pairedSkewExp_mem_orthogonalGroup
    (X : Matrix Source48Label Source48Label ℝ)
    (hX : X.transpose = -X) (t : ℝ) :
    exp (t • X) ∈ Matrix.orthogonalGroup Source48Label ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff,
    pairedSkewExp_transpose_eq_inv X hX t]
  have hdet : IsUnit (exp (t • X)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp (t • X))
  exact Matrix.mul_nonsing_inv _ hdet

/-- The image of the actual canonical V9T real LieHom generates a
one-parameter orthogonal matrix family on the original 48 labels. -/
theorem coordinateToPairedCanonicalSkewLieHom_exp_mem_orthogonalGroup
    (A : skewAdjointMatricesLieSubalgebra
      (1 : Matrix SpaceIndex SpaceIndex ℝ)) (t : ℝ) :
    exp (t • ((coordinateToPairedCanonicalSkewLieHom A) :
       Matrix Source48Label Source48Label ℝ)) ∈
      Matrix.orthogonalGroup Source48Label ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff,
    coordinateToPairedCanonicalSkewLieHom_exp_transpose_eq_inv A t]
  have hdet :
      IsUnit (exp (t • ((coordinateToPairedCanonicalSkewLieHom A) :
        Matrix Source48Label Source48Label ℝ))).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.isUnit_exp _)
  exact Matrix.mul_nonsing_inv _ hdet

/-- Every original normalized paired plane generates actual
orthogonal matrices, with no substitution of the color-major labels. -/
theorem normalizedPairedPlane_exp_mem_orthogonalGroup
    (r s : SpaceIndex) (t : ℝ) :
    exp (t • normalizedPairedPlane r s) ∈
      Matrix.orthogonalGroup Source48Label ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff,
    normalizedPairedPlane_exp_transpose_eq_inv r s t]
  have hdet : IsUnit (exp (t • normalizedPairedPlane r s)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)
  exact Matrix.mul_nonsing_inv _ hdet

#print axioms pairedSkewExp_mem_orthogonalGroup
#print axioms coordinateToPairedCanonicalSkewLieHom_exp_mem_orthogonalGroup
#print axioms normalizedPairedPlane_exp_mem_orthogonalGroup

end
end FCP.BFSSPairedSpin9Plane
