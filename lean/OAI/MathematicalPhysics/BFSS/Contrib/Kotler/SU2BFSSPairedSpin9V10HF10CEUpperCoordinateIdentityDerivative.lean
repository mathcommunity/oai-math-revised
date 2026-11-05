import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CDContinuousNativeModel
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-! F10CE: the actual ordered-word upper-coordinate map has identity derivative.
This is an ordinary finite-parameter map and an inverse-function prerequisite,
not a source subgroup atlas or a source local kernel/coverage theorem.
Candidate until fresh strict compilation and independent audit pass. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open scoped Matrix.Norms.Elementwise

/-- Continuous extraction of original enumerated upper entries from any native matrix. -/
noncomputable def source9OrderedUpperProjection :
    Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] (Fin 36 → ℝ) :=
  ContinuousLinearMap.pi (fun i : Fin 36 =>
    (ContinuousLinearMap.proj (source9StrictPlaneColumn i) :
      (SpaceIndex → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj (source9StrictPlaneRow i) :
          (SpaceIndex → SpaceIndex → ℝ) →L[ℝ] (SpaceIndex → ℝ)))

theorem source9OrderedUpperProjection_apply
    (A : Matrix SpaceIndex SpaceIndex ℝ) (i : Fin 36) :
    source9OrderedUpperProjection A i =
      A (source9StrictPlaneRow i) (source9StrictPlaneColumn i) := rfl

/-- Upper-coordinate projection of the actual natural matrix image of the actual source word. -/
noncomputable def source9OrderedUpperCoordinateMap (t : Fin 36 → ℝ) : Fin 36 → ℝ :=
  source9OrderedUpperProjection
    ((source9SpinVectorOrthogonalHom (source9OrderedStrictPlaneWord t)) :
      Matrix SpaceIndex SpaceIndex ℝ)

theorem source9OrderedUpperCoordinateMap_zero : source9OrderedUpperCoordinateMap 0 = 0 := by
  funext i
  change ((source9SpinVectorOrthogonalHom (source9OrderedStrictPlaneWord 0)) :
    Matrix SpaceIndex SpaceIndex ℝ) (source9StrictPlaneRow i) (source9StrictPlaneColumn i) = 0
  rw [source9OrderedStrictPlaneWord_zero, map_one]
  change (1 : Matrix SpaceIndex SpaceIndex ℝ)
    (source9StrictPlaneRow i) (source9StrictPlaneColumn i) = 0
  simp only [Matrix.one_apply, ite_eq_right (source9StrictPlaneEnumeration_ne i)]

/-- Literal equality of continuous linear maps, using actual derivative coordinate recovery. -/
theorem source9OrderedUpperProjection_wordVelocity :
    source9OrderedUpperProjection.comp
      (source9PlaneWordMatrixVelocity source9StrictPlaneRow source9StrictPlaneColumn
        (List.finRange 36)) = ContinuousLinearMap.id ℝ (Fin 36 → ℝ) := by
  apply ContinuousLinearMap.ext
  intro v
  funext i
  change source9PlaneWordMatrixVelocity source9StrictPlaneRow source9StrictPlaneColumn
    (List.finRange 36) v (source9StrictPlaneRow i) (source9StrictPlaneColumn i) = v i
  have hmap := source9OrderedStrictPlaneWord_matrix_hasFDerivAt_zero.fderiv
  have heval := congrArg
    (fun L : (Fin 36 → ℝ) →L[ℝ] Matrix SpaceIndex SpaceIndex ℝ =>
      L v (source9StrictPlaneRow i) (source9StrictPlaneColumn i)) hmap
  exact heval.symm.trans (source9OrderedStrictPlaneWord_matrix_fderiv_zero_upper v i)

/-- The entire actual upper-coordinate map has the literal identity derivative at zero. -/
theorem source9OrderedUpperCoordinateMap_hasFDerivAt_zero :
    HasFDerivAt source9OrderedUpperCoordinateMap
      (ContinuousLinearMap.id ℝ (Fin 36 → ℝ)) 0 := by
  have h := source9OrderedUpperProjection.hasFDerivAt.comp (0 : Fin 36 → ℝ)
    source9OrderedStrictPlaneWord_matrix_hasFDerivAt_zero
  change HasFDerivAt source9OrderedUpperCoordinateMap
    (source9OrderedUpperProjection.comp
      (source9PlaneWordMatrixVelocity source9StrictPlaneRow source9StrictPlaneColumn
        (List.finRange 36))) 0 at h
  rw [source9OrderedUpperProjection_wordVelocity] at h
  exact h

theorem source9OrderedUpperCoordinateMap_fderiv_zero :
    fderiv ℝ source9OrderedUpperCoordinateMap 0 =
      ContinuousLinearMap.id ℝ (Fin 36 → ℝ) :=
  source9OrderedUpperCoordinateMap_hasFDerivAt_zero.fderiv

#print axioms source9OrderedUpperProjection
#print axioms source9OrderedUpperProjection_apply
#print axioms source9OrderedUpperCoordinateMap
#print axioms source9OrderedUpperCoordinateMap_zero
#print axioms source9OrderedUpperProjection_wordVelocity
#print axioms source9OrderedUpperCoordinateMap_hasFDerivAt_zero
#print axioms source9OrderedUpperCoordinateMap_fderiv_zero
end
end FCP.BFSSPairedSpin9Clifford
