import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BPSourceVectorLinearRepresentation
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
F10BQ — preservation of the actual source quadratic form.

Candidate only until strict compilation and independent type/axiom audit.
Use the accepted representation's exact actual Clifford conjugation,
the source Clifford square law, and scalar faithfulness. Package each
actual source Spin element as an isometric equivalence for the same
source9Quadratic with inverse given by the existing representation at g⁻¹.

No new norm, topology or group structure is registered. An orthogonal
matrix homomorphism, determinant-one membership and a full manifold
differential remain separate obligations.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum

/-- The accepted actual source-vector representation preserves the original quadratic form. -/
theorem source9SpinVectorRepresentation_preserves_quadratic
    (g : spinGroup source9Quadratic) (z : SpaceIndex → ℝ) :
    source9Quadratic (source9SpinVectorRepresentation g z) = source9Quadratic z := by
  change source9Quadratic (source9SpinVectorConjugation g z) = source9Quadratic z
  have hleft :
      ((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic) *
        (g : CliffordAlgebra source9Quadratic) = 1 :=
    congrArg (fun x : spinGroup source9Quadratic =>
      (x : CliffordAlgebra source9Quadratic)) (inv_mul_cancel g)
  have hright :
      (g : CliffordAlgebra source9Quadratic) *
        ((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic) = 1 :=
    congrArg (fun x : spinGroup source9Quadratic =>
      (x : CliffordAlgebra source9Quadratic)) (mul_inv_cancel g)
  apply FaithfulSMul.algebraMap_injective ℝ (CliffordAlgebra source9Quadratic)
  calc
    algebraMap ℝ (CliffordAlgebra source9Quadratic)
        (source9Quadratic (source9SpinVectorConjugation g z)) =
        CliffordAlgebra.ι source9Quadratic (source9SpinVectorConjugation g z) *
          CliffordAlgebra.ι source9Quadratic (source9SpinVectorConjugation g z) :=
      (CliffordAlgebra.ι_sq_scalar (Q := source9Quadratic)
        (source9SpinVectorConjugation g z)).symm
    _ = ((g : CliffordAlgebra source9Quadratic) * CliffordAlgebra.ι source9Quadratic z *
          ((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic)) *
        ((g : CliffordAlgebra source9Quadratic) * CliffordAlgebra.ι source9Quadratic z *
          ((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic)) := by
      simp only [source9SpinVectorConjugation_ι]
    _ = (g : CliffordAlgebra source9Quadratic) *
        (CliffordAlgebra.ι source9Quadratic z *
          (((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic) *
            (g : CliffordAlgebra source9Quadratic)) *
          CliffordAlgebra.ι source9Quadratic z) *
        ((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic) := by
      simp only [mul_assoc]
    _ = (g : CliffordAlgebra source9Quadratic) *
        (CliffordAlgebra.ι source9Quadratic z * CliffordAlgebra.ι source9Quadratic z) *
        ((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic) := by
      rw [hleft, mul_one]
    _ = (g : CliffordAlgebra source9Quadratic) *
        algebraMap ℝ (CliffordAlgebra source9Quadratic) (source9Quadratic z) *
        ((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic) := by
      rw [CliffordAlgebra.ι_sq_scalar (Q := source9Quadratic) z]
    _ = algebraMap ℝ (CliffordAlgebra source9Quadratic) (source9Quadratic z) := by
      rw [← Algebra.commutes (source9Quadratic z) (g : CliffordAlgebra source9Quadratic),
        mul_assoc, hright, mul_one]

/-- Each actual source Spin element is an isometry of the same actual nine-vector quadratic space. -/
noncomputable def source9SpinVectorQuadraticIsometryEquiv
    (g : spinGroup source9Quadratic) :
    source9Quadratic.IsometryEquiv source9Quadratic where
  toLinearEquiv :=
    { source9SpinVectorRepresentation g with
      toFun := source9SpinVectorRepresentation g
      invFun := source9SpinVectorRepresentation g⁻¹
      left_inv := Representation.inv_self_apply source9SpinVectorRepresentation g
      right_inv := Representation.self_inv_apply source9SpinVectorRepresentation g }
  map_app' := source9SpinVectorRepresentation_preserves_quadratic g

#print axioms source9SpinVectorRepresentation_preserves_quadratic
#print axioms source9SpinVectorQuadraticIsometryEquiv

end
end FCP.BFSSPairedSpin9Clifford
