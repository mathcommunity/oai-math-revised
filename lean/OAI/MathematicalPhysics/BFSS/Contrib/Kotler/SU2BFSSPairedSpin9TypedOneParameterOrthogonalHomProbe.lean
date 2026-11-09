import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9OneParameterOrthogonalFlowProbe

/-!
K1D18V9X — an actual typed one-parameter group homomorphism
from the additive real parameters (in Multiplicative notation) into
Mathlib's orthogonal group on the *original* paired-Fock 48 labels.

This uses accepted V9V orthogonal membership and V9W composition/zero.
It is NOT the integration of the whole Spin(9) group, an SO(48)
determinant-one proof, a Spin(48) lift, or a continuity theorem.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open NormedSpace

/-- For an arbitrary skew matrix on the exact original 48 labels,
the additive real parameters, written multiplicatively, map into
the genuine orthogonal group under the matrix exponential. -/
noncomputable def pairedSkewOneParameterOrthogonalHom
    (X : Matrix Source48Label Source48Label ℝ)
    (hX : X.transpose = -X) :
    Multiplicative ℝ →* Matrix.orthogonalGroup Source48Label ℝ where
  toFun := fun t =>
    ⟨exp ((Multiplicative.toAdd t) • X),
      pairedSkewExp_mem_orthogonalGroup X hX (Multiplicative.toAdd t)⟩
  map_one' := by
    apply Subtype.ext
    change exp ((0 : ℝ) • X) = (1 : Matrix Source48Label Source48Label ℝ)
    exact pairedMatrixExp_zero X
  map_mul' := by
    intro s t
    apply Subtype.ext
    change exp (((Multiplicative.toAdd s) + (Multiplicative.toAdd t)) • X) =
      exp ((Multiplicative.toAdd s) • X) * exp ((Multiplicative.toAdd t) • X)
    exact pairedMatrixExp_add X (Multiplicative.toAdd s) (Multiplicative.toAdd t)

/-- Exact underlying matrix of the typed one-parameter orthogonal hom. -/
theorem pairedSkewOneParameterOrthogonalHom_apply
    (X : Matrix Source48Label Source48Label ℝ)
    (hX : X.transpose = -X) (t : ℝ) :
    ((pairedSkewOneParameterOrthogonalHom X hX
      (Multiplicative.ofAdd t)) : Matrix Source48Label Source48Label ℝ) =
      exp (t • X) := rfl

/-- Genuine one-parameter orthogonal-group hom for the source-exact
normalized paired-Fock plane generator. -/
noncomputable def normalizedPairedPlaneOneParameterOrthogonalHom
    (r s : SpaceIndex) :
    Multiplicative ℝ →* Matrix.orthogonalGroup Source48Label ℝ :=
  pairedSkewOneParameterOrthogonalHom
    (normalizedPairedPlane r s) (normalizedPairedPlane_transpose r s)

/-- The normalized generator's group-valued hom is exactly its
original paired-Fock 48-by-48 matrix exponential. -/
theorem normalizedPairedPlaneOneParameterOrthogonalHom_apply
    (r s : SpaceIndex) (t : ℝ) :
    ((normalizedPairedPlaneOneParameterOrthogonalHom r s
      (Multiplicative.ofAdd t)) : Matrix Source48Label Source48Label ℝ) =
      exp (t • normalizedPairedPlane r s) := rfl

/-- Genuine typed one-parameter orthogonal hom for each image of
the qualified canonical so(9) -> so(48) LieHom. No group integration
claim about the full nine-dimensional rotation or Spin group. -/
noncomputable def coordinateToPairedCanonicalOneParameterOrthogonalHom
    (A : skewAdjointMatricesLieSubalgebra
      (1 : Matrix SpaceIndex SpaceIndex ℝ)) :
    Multiplicative ℝ →* Matrix.orthogonalGroup Source48Label ℝ := by
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
  exact pairedSkewOneParameterOrthogonalHom
    (X : Matrix Source48Label Source48Label ℝ) hX

/-- Underlying source-exact matrix of the canonical LieHom image's
one-parameter orthogonal hom. -/
theorem coordinateToPairedCanonicalOneParameterOrthogonalHom_apply
    (A : skewAdjointMatricesLieSubalgebra
      (1 : Matrix SpaceIndex SpaceIndex ℝ)) (t : ℝ) :
    ((coordinateToPairedCanonicalOneParameterOrthogonalHom A
      (Multiplicative.ofAdd t)) : Matrix Source48Label Source48Label ℝ) =
      exp (t • ((coordinateToPairedCanonicalSkewLieHom A) :
        Matrix Source48Label Source48Label ℝ)) := by
  rfl

#print axioms pairedSkewOneParameterOrthogonalHom
#print axioms pairedSkewOneParameterOrthogonalHom_apply
#print axioms normalizedPairedPlaneOneParameterOrthogonalHom
#print axioms normalizedPairedPlaneOneParameterOrthogonalHom_apply
#print axioms coordinateToPairedCanonicalOneParameterOrthogonalHom
#print axioms coordinateToPairedCanonicalOneParameterOrthogonalHom_apply

end
end FCP.BFSSPairedSpin9Plane
