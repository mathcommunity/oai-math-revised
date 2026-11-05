import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CFSmoothStrictUpperCoordinateMap
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! F10CG: parameter-space local inversion of the actual upper-coordinate map.
Use the qualified strict derivative with the identity continuous linear equivalence.
This does not establish source Spin coverage, local kernel control or a subgroup atlas.
Candidate until complete strict source and independent audit success. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open scoped Matrix.Norms.Elementwise

/-- Expose the invertible derivative in the constructor's continuous-equivalence interface. -/
theorem source9OrderedUpperCoordinateMap_hasStrictFDerivAt_refl :
    HasStrictFDerivAt source9OrderedUpperCoordinateMap
      ((ContinuousLinearEquiv.refl ℝ (Fin 36 → ℝ)) :
        (Fin 36 → ℝ) →L[ℝ] (Fin 36 → ℝ)) 0 :=
  source9OrderedUpperCoordinateMap_hasStrictFDerivAt_zero

/-- The actual finite-parameter upper-coordinate map as an open partial homeomorphism. -/
noncomputable def source9OrderedUpperCoordinateLocalHomeomorph :
    OpenPartialHomeomorph (Fin 36 → ℝ) (Fin 36 → ℝ) :=
  source9OrderedUpperCoordinateMap_hasStrictFDerivAt_refl.toOpenPartialHomeomorph
    (f' := ContinuousLinearEquiv.refl ℝ (Fin 36 → ℝ)) source9OrderedUpperCoordinateMap

/-- The forward function is exactly the accepted actual upper-coordinate map. -/
theorem source9OrderedUpperCoordinateLocalHomeomorph_coe :
    (source9OrderedUpperCoordinateLocalHomeomorph : (Fin 36 → ℝ) → (Fin 36 → ℝ)) =
      source9OrderedUpperCoordinateMap :=
  source9OrderedUpperCoordinateMap_hasStrictFDerivAt_refl.toOpenPartialHomeomorph_coe
    (f' := ContinuousLinearEquiv.refl ℝ (Fin 36 → ℝ))

theorem source9OrderedUpperCoordinateLocalHomeomorph_zero_mem_source :
    (0 : Fin 36 → ℝ) ∈ source9OrderedUpperCoordinateLocalHomeomorph.source :=
  source9OrderedUpperCoordinateMap_hasStrictFDerivAt_refl.mem_toOpenPartialHomeomorph_source
    (f' := ContinuousLinearEquiv.refl ℝ (Fin 36 → ℝ))

theorem source9OrderedUpperCoordinateLocalHomeomorph_zero_mem_target :
    (0 : Fin 36 → ℝ) ∈ source9OrderedUpperCoordinateLocalHomeomorph.target := by
  have h : source9OrderedUpperCoordinateMap (0 : Fin 36 → ℝ) ∈
      source9OrderedUpperCoordinateLocalHomeomorph.target :=
    source9OrderedUpperCoordinateMap_hasStrictFDerivAt_refl.image_mem_toOpenPartialHomeomorph_target
      (f' := ContinuousLinearEquiv.refl ℝ (Fin 36 → ℝ))
  rw [source9OrderedUpperCoordinateMap_zero] at h
  exact h

/-- The partial inverse recovers each parameter on the actual source neighborhood. -/
theorem source9OrderedUpperCoordinateLocalHomeomorph_left_inv
    (t : Fin 36 → ℝ) (ht : t ∈ source9OrderedUpperCoordinateLocalHomeomorph.source) :
    source9OrderedUpperCoordinateLocalHomeomorph.symm (source9OrderedUpperCoordinateMap t) = t := by
  have heq := congrFun source9OrderedUpperCoordinateLocalHomeomorph_coe t
  have h := source9OrderedUpperCoordinateLocalHomeomorph.left_inv ht
  exact (congrArg (fun y : Fin 36 → ℝ =>
    source9OrderedUpperCoordinateLocalHomeomorph.symm y) heq).symm.trans h

/-- The actual upper-coordinate map recovers each coordinate on the target neighborhood. -/
theorem source9OrderedUpperCoordinateLocalHomeomorph_right_inv
    (y : Fin 36 → ℝ) (hy : y ∈ source9OrderedUpperCoordinateLocalHomeomorph.target) :
    source9OrderedUpperCoordinateMap (source9OrderedUpperCoordinateLocalHomeomorph.symm y) = y := by
  have heq := congrFun source9OrderedUpperCoordinateLocalHomeomorph_coe
    (source9OrderedUpperCoordinateLocalHomeomorph.symm y)
  exact heq.symm.trans (source9OrderedUpperCoordinateLocalHomeomorph.right_inv hy)

#print axioms source9OrderedUpperCoordinateMap_hasStrictFDerivAt_refl
#print axioms source9OrderedUpperCoordinateLocalHomeomorph
#print axioms source9OrderedUpperCoordinateLocalHomeomorph_coe
#print axioms source9OrderedUpperCoordinateLocalHomeomorph_zero_mem_source
#print axioms source9OrderedUpperCoordinateLocalHomeomorph_zero_mem_target
#print axioms source9OrderedUpperCoordinateLocalHomeomorph_left_inv
#print axioms source9OrderedUpperCoordinateLocalHomeomorph_right_inv
end
end FCP.BFSSPairedSpin9Clifford
