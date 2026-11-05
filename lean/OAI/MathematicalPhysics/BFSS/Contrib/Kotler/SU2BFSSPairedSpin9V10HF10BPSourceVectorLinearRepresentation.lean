import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BOSourceVectorConjugationDerivative
import Mathlib.RepresentationTheory.Basic

/-!
F10BP — exact algebraic source Spin representation on original nine-vectors.

Candidate only until strict compilation and independent type/axiom audit.
Reuse F10BO's explicit vector recovery and exact conjugation embedding.
The left inverse makes the vector embedding injective; linearity and the
actual group conjugation laws then package as Mathlib Representation.

No new norm or topology is registered. This is an algebraic representation,
not yet an orthogonal-matrix homomorphism, smooth action, manifold tangent
identification or global differential theorem.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum

/-- The actual nine-vector Clifford embedding is injective by the accepted explicit left inverse. -/
theorem source9CliffordVectorEmbedding_injective :
    Function.Injective (CliffordAlgebra.ι source9Quadratic :
      (SpaceIndex → ℝ) → CliffordAlgebra source9Quadratic) := by
  intro z w h
  have hp := congrArg source9CliffordVectorProjection h
  simpa only [source9CliffordVectorProjection_ι] using hp

/-- Actual vector conjugation by a fixed source Spin element is real-linear. -/
noncomputable def source9SpinVectorLinearMap (g : spinGroup source9Quadratic) :
    (SpaceIndex → ℝ) →ₗ[ℝ] (SpaceIndex → ℝ) where
  toFun := source9SpinVectorConjugation g
  map_add' := by
    intro z w
    simp only [source9SpinVectorConjugation, map_add, mul_add, add_mul]
  map_smul' := by
    intro c z
    simp only [source9SpinVectorConjugation, map_smul, mul_smul_comm, smul_mul_assoc,
      RingHom.id_apply]

/-- The actual source identity acts as the identity on every original nine-vector. -/
theorem source9SpinVectorConjugation_one (z : SpaceIndex → ℝ) :
    source9SpinVectorConjugation (1 : spinGroup source9Quadratic) z = z := by
  apply source9CliffordVectorEmbedding_injective
  rw [source9SpinVectorConjugation_ι]
  simp

/-- Multiplication acts by the same-order composition required by Mathlib representations. -/
theorem source9SpinVectorConjugation_mul
    (g h : spinGroup source9Quadratic) (z : SpaceIndex → ℝ) :
    source9SpinVectorConjugation (g * h) z =
      source9SpinVectorConjugation g (source9SpinVectorConjugation h z) := by
  apply source9CliffordVectorEmbedding_injective
  rw [source9SpinVectorConjugation_ι, source9SpinVectorConjugation_ι,
    source9SpinVectorConjugation_ι, mul_inv_rev]
  change ((g : CliffordAlgebra source9Quadratic) *
      (h : CliffordAlgebra source9Quadratic)) * CliffordAlgebra.ι source9Quadratic z *
      (((h⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic) *
        ((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic)) =
    (g : CliffordAlgebra source9Quadratic) *
      ((h : CliffordAlgebra source9Quadratic) * CliffordAlgebra.ι source9Quadratic z *
        ((h⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic)) *
      ((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic)
  simp only [mul_assoc]

/-- The actual source Spin group acts linearly on exactly the original real nine-vector carrier. -/
noncomputable def source9SpinVectorRepresentation :
    Representation ℝ (spinGroup source9Quadratic) (SpaceIndex → ℝ) where
  toFun := source9SpinVectorLinearMap
  map_one' := by
    apply LinearMap.ext
    intro z
    change source9SpinVectorConjugation (1 : spinGroup source9Quadratic) z = z
    exact source9SpinVectorConjugation_one z
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro z
    change source9SpinVectorConjugation (g * h) z =
      source9SpinVectorConjugation g (source9SpinVectorConjugation h z)
    exact source9SpinVectorConjugation_mul g h z

#print axioms source9CliffordVectorEmbedding_injective
#print axioms source9SpinVectorLinearMap
#print axioms source9SpinVectorConjugation_one
#print axioms source9SpinVectorConjugation_mul
#print axioms source9SpinVectorRepresentation

end
end FCP.BFSSPairedSpin9Clifford
