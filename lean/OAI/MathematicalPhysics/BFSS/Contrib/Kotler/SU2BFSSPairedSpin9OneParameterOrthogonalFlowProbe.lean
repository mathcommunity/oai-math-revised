import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9OrthogonalGroupMembershipProbe

/-!
K1D18V9W — original Fock-paired real one-parameter exponential
composition laws, building on qualified V9V orthogonal membership.

Mathlib's pinned Matrix.exp_add_of_commute is applied only after
a genuine commutation proof for scalar multiples of the *same*
source-exact matrix. No indexing substitution, unproved group
integration, topological covering, or physical spectral claim.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open NormedSpace

/-- Matrix-exponential composition on the *original* paired-Fock
48-label carrier, for scalar multiples of one arbitrary matrix. -/
theorem pairedMatrixExp_add
    (X : Matrix Source48Label Source48Label ℝ) (s t : ℝ) :
    exp ((s + t) • X) = exp (s • X) * exp (t • X) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute (s • X) (t • X)
    (((Commute.refl X).smul_left s).smul_right t)

/-- Identity at parameter zero for the genuine matrix exponential. -/
theorem pairedMatrixExp_zero
    (X : Matrix Source48Label Source48Label ℝ) :
    exp ((0 : ℝ) • X) = 1 := by
  simp

/-- Inverse at the negative parameter; this is a genuine
matrix inverse, not a merely formal reciprocal. -/
theorem pairedMatrixExp_neg
    (X : Matrix Source48Label Source48Label ℝ) (t : ℝ) :
    exp ((-t) • X) = (exp (t • X))⁻¹ := by
  rw [neg_smul, Matrix.exp_neg]

/-- The accepted canonical source-nine to source-paired-forty-eight
LieHom induces the exact one-parameter matrix composition identity
for each input element, with the source-native labels preserved. -/
theorem coordinateToPairedCanonicalSkewLieHom_exp_add
    (A : skewAdjointMatricesLieSubalgebra
      (1 : Matrix SpaceIndex SpaceIndex ℝ)) (s t : ℝ) :
    exp ((s + t) • ((coordinateToPairedCanonicalSkewLieHom A) :
      Matrix Source48Label Source48Label ℝ)) =
      exp (s • ((coordinateToPairedCanonicalSkewLieHom A) :
        Matrix Source48Label Source48Label ℝ)) *
      exp (t • ((coordinateToPairedCanonicalSkewLieHom A) :
        Matrix Source48Label Source48Label ℝ)) := by
  exact pairedMatrixExp_add _ s t

/-- One-parameter composition law for each original normalized
paired-Fock Spin(9) plane generator, including diagonal and reversed
index order. The individual exponentials are orthogonal by V9V. -/
theorem normalizedPairedPlane_exp_add
    (r s : SpaceIndex) (u v : ℝ) :
    exp ((u + v) • normalizedPairedPlane r s) =
      exp (u • normalizedPairedPlane r s) *
      exp (v • normalizedPairedPlane r s) := by
  exact pairedMatrixExp_add _ u v

#print axioms pairedMatrixExp_add
#print axioms pairedMatrixExp_zero
#print axioms pairedMatrixExp_neg
#print axioms coordinateToPairedCanonicalSkewLieHom_exp_add
#print axioms normalizedPairedPlane_exp_add

end
end FCP.BFSSPairedSpin9Plane
