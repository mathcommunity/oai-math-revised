import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BQSourceVectorQuadraticIsometry
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Linarith

/-!
F10BR — exact matrix realization of the actual nine-vector source action.

Candidate only until strict compilation and independent type/axiom audit.
Polarize the accepted quadratic preservation to obtain dot-product
preservation. Use Mathlib's canonical coordinate linear-map/matrix algebra
equivalence, with the original Pi.single coordinate vectors, and prove
orthogonality from A.transpose * A = 1.

The target is exactly Matrix.orthogonalGroup SpaceIndex ℝ. Determinant-one
membership, a group-kernel classification, smoothness, manifold tangent
identification and the full F10BC differential remain separate.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum

/-- The actual source-vector representation preserves the original real dot product on all vectors. -/
theorem source9SpinVectorRepresentation_preserves_dotProduct
    (g : spinGroup source9Quadratic) (z w : SpaceIndex → ℝ) :
    dotProduct (source9SpinVectorRepresentation g z) (source9SpinVectorRepresentation g w) =
      dotProduct z w := by
  have hz := source9SpinVectorRepresentation_preserves_quadratic g z
  have hw := source9SpinVectorRepresentation_preserves_quadratic g w
  have hzw := source9SpinVectorRepresentation_preserves_quadratic g (z + w)
  rw [map_add] at hzw
  simp only [source9Quadratic_eq_dot, add_dotProduct, dotProduct_add] at hz hw hzw
  have hcross :
      dotProduct (source9SpinVectorRepresentation g w) (source9SpinVectorRepresentation g z) =
        dotProduct (source9SpinVectorRepresentation g z) (source9SpinVectorRepresentation g w) :=
    dotProduct_comm _ _
  have hcross0 : dotProduct w z = dotProduct z w := dotProduct_comm _ _
  rw [hcross, hcross0] at hzw
  linarith

/-- Canonical matrix monoid homomorphism of the accepted actual original-nine-vector representation. -/
noncomputable def source9SpinVectorMatrixHom :
    spinGroup source9Quadratic →* Matrix SpaceIndex SpaceIndex ℝ :=
  ((LinearMap.toMatrixAlgEquiv' :
    ((SpaceIndex → ℝ) →ₗ[ℝ] (SpaceIndex → ℝ)) ≃ₐ[ℝ]
      Matrix SpaceIndex SpaceIndex ℝ).toAlgHom.toMonoidHom).comp source9SpinVectorRepresentation

/-- Matrix evaluation is exactly the accepted source action on every original nine-vector. -/
theorem source9SpinVectorMatrixHom_mulVec
    (g : spinGroup source9Quadratic) (z : SpaceIndex → ℝ) :
    (source9SpinVectorMatrixHom g).mulVec z = source9SpinVectorRepresentation g z := by
  change (LinearMap.toMatrix' (source9SpinVectorRepresentation g)).mulVec z = _
  exact LinearMap.toMatrix'_mulVec (source9SpinVectorRepresentation g) z

/-- The exact canonical source-action matrix is in the native nine-dimensional orthogonal group. -/
theorem source9SpinVectorMatrixHom_mem_orthogonalGroup
    (g : spinGroup source9Quadratic) :
    source9SpinVectorMatrixHom g ∈ Matrix.orthogonalGroup SpaceIndex ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  apply Matrix.ext
  intro i j
  change dotProduct
      (source9SpinVectorRepresentation g (source9CoordinateVector i))
      (source9SpinVectorRepresentation g (source9CoordinateVector j)) =
    (1 : Matrix SpaceIndex SpaceIndex ℝ) i j
  rw [source9SpinVectorRepresentation_preserves_dotProduct]
  simp only [source9CoordinateVector, single_dotProduct, one_mul,
    Matrix.one_apply, Pi.single_apply]

/-- Global algebraic actual source Spin homomorphism into the original-nine-vector orthogonal group. -/
noncomputable def source9SpinVectorOrthogonalHom :
    spinGroup source9Quadratic →* Matrix.orthogonalGroup SpaceIndex ℝ where
  toFun g := ⟨source9SpinVectorMatrixHom g, source9SpinVectorMatrixHom_mem_orthogonalGroup g⟩
  map_one' := by
    apply Subtype.ext
    change source9SpinVectorMatrixHom (1 : spinGroup source9Quadratic) = 1
    exact map_one source9SpinVectorMatrixHom
  map_mul' := by
    intro g h
    apply Subtype.ext
    change source9SpinVectorMatrixHom (g * h) =
      source9SpinVectorMatrixHom g * source9SpinVectorMatrixHom h
    exact map_mul source9SpinVectorMatrixHom g h

/-- The orthogonal homomorphism's underlying matrix acts by literal actual source-vector conjugation. -/
theorem source9SpinVectorOrthogonalHom_mulVec
    (g : spinGroup source9Quadratic) (z : SpaceIndex → ℝ) :
    ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ).mulVec z =
      source9SpinVectorRepresentation g z := by
  change (source9SpinVectorMatrixHom g).mulVec z = _
  exact source9SpinVectorMatrixHom_mulVec g z

#print axioms source9SpinVectorRepresentation_preserves_dotProduct
#print axioms source9SpinVectorMatrixHom
#print axioms source9SpinVectorMatrixHom_mulVec
#print axioms source9SpinVectorMatrixHom_mem_orthogonalGroup
#print axioms source9SpinVectorOrthogonalHom
#print axioms source9SpinVectorOrthogonalHom_mulVec

end
end FCP.BFSSPairedSpin9Clifford
