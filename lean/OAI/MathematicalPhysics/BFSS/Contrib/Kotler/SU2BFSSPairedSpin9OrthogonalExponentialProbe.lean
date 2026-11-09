import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9CanonicalSkewLieHomProbe
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
K1D18V9U — original paired-Fock 48-real infinitesimal rotations
have matrix exponentials whose transpose equals their inverse.

This is an analytic bridge from the accepted source-exact V9T
Lie algebra homomorphism to individual orthogonal matrix flows,
using the pinned Mathlib matrix exponential, not a substitute
gamma representation or an unproved Lie integration theorem.

It does NOT construct a continuous group homomorphism
Spin(9) → SO(48), a Spin(48) lift, a covering map, or
any BFSS gauge-covariant/spectral statement.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open NormedSpace

/-- Exact real Fock-paired skew input yields a matrix exponential with
transpose equal to inverse, at every real parameter. -/
theorem pairedSkewExp_transpose_eq_inv
    (X : Matrix Source48Label Source48Label ℝ)
    (hX : X.transpose = -X) (t : ℝ) :
    (exp (t • X)).transpose = (exp (t • X))⁻¹ := by
  calc
    (exp (t • X)).transpose =
        exp ((t • X).transpose) := (Matrix.exp_transpose _).symm
    _ = exp (-(t • X)) := by rw [Matrix.transpose_smul, hX, smul_neg]
    _ = (exp (t • X))⁻¹ := Matrix.exp_neg _

/-- Apply the analytic orthogonality identity to the genuine V9T
source-native-to-original-paired Mathlib LieHom, for arbitrary
canonical skew source inputs, with no reindexing. -/
theorem coordinateToPairedCanonicalSkewLieHom_exp_transpose_eq_inv
    (A : skewAdjointMatricesLieSubalgebra
      (1 : Matrix SpaceIndex SpaceIndex ℝ)) (t : ℝ) :
    (exp (t • ((coordinateToPairedCanonicalSkewLieHom A) :
       Matrix Source48Label Source48Label ℝ))).transpose =
      (exp (t • ((coordinateToPairedCanonicalSkewLieHom A) :
       Matrix Source48Label Source48Label ℝ)))⁻¹ := by
  let X : skewAdjointMatricesLieSubalgebra
      (1 : Matrix Source48Label Source48Label ℝ) :=
    coordinateToPairedCanonicalSkewLieHom A
  have hX : (X : Matrix Source48Label Source48Label ℝ).transpose =
      -(X : Matrix Source48Label Source48Label ℝ) := by
    have hm : (X : Matrix Source48Label Source48Label ℝ) ∈
        pairedSkewLieSubalgebra := by
      rw [pairedSkewLieSubalgebra_eq_mathlib]
      exact X.property
    change (X : Matrix Source48Label Source48Label ℝ).transpose =
      -(X : Matrix Source48Label Source48Label ℝ) at hm
    exact hm
  exact pairedSkewExp_transpose_eq_inv
    (X : Matrix Source48Label Source48Label ℝ) hX t

/-- The exact original normalized paired-Fock Spin(9) plane
generators exponentiate to matrices with transpose equal to inverse,
including coincident and reversed index cases. -/
theorem normalizedPairedPlane_exp_transpose_eq_inv
    (r s : SpaceIndex) (t : ℝ) :
    (exp (t • normalizedPairedPlane r s)).transpose =
      (exp (t • normalizedPairedPlane r s))⁻¹ :=
  pairedSkewExp_transpose_eq_inv
    (normalizedPairedPlane r s)
    (normalizedPairedPlane_transpose r s) t

#print axioms pairedSkewExp_transpose_eq_inv
#print axioms coordinateToPairedCanonicalSkewLieHom_exp_transpose_eq_inv
#print axioms normalizedPairedPlane_exp_transpose_eq_inv

end
end FCP.BFSSPairedSpin9Plane
