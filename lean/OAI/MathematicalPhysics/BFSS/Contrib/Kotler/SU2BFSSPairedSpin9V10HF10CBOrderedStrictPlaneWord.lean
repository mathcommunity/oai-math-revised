import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CANativeStrictPlaneModel
import Mathlib.Data.Fintype.EquivFin

/-! F10CB: one chosen enumeration and actual 36-factor source word.
The enumeration is a fixed named finite bijection, not a lexicographic claim.
Derivatives retain the exact listed native-plane sum. Reindexing that sum
through CA, continuity of the model and charts remain separate obligations.
Candidate until fresh strict compilation and independent audit pass. -/

set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open FCP.BFSSPairedSpin9Plane
open scoped Matrix.Norms.Elementwise

/-- A single chosen enumeration of all 36 original increasing spatial pairs. -/
noncomputable def source9StrictPlaneEnumeration : Fin 36 ≃ source9StrictPlaneIndex :=
  (Fintype.equivFinOfCardEq source9StrictPlaneIndex_card).symm

noncomputable def source9StrictPlaneRow (i : Fin 36) : SpaceIndex :=
  (source9StrictPlaneEnumeration i).val.1
noncomputable def source9StrictPlaneColumn (i : Fin 36) : SpaceIndex :=
  (source9StrictPlaneEnumeration i).val.2

/-- No plane is omitted or repeated by the chosen enumeration. -/
theorem source9StrictPlaneEnumeration_bijective :
    Function.Bijective source9StrictPlaneEnumeration := source9StrictPlaneEnumeration.bijective

/-- Every enumerated actual source curve has the required distinct native labels. -/
theorem source9StrictPlaneEnumeration_ne (i : Fin 36) :
    source9StrictPlaneRow i ≠ source9StrictPlaneColumn i :=
  (source9StrictPlaneEnumeration i).property.ne

/-- Actual source group word in increasing parameter-index order. -/
noncomputable def source9OrderedStrictPlaneWord (t : Fin 36 → ℝ) :
    spinGroup source9Quadratic :=
  source9PlaneSpinWord source9StrictPlaneRow source9StrictPlaneColumn
    source9StrictPlaneEnumeration_ne t (List.finRange 36)

theorem source9OrderedStrictPlaneWord_zero : source9OrderedStrictPlaneWord 0 = 1 :=
  source9PlaneSpinWord_zero source9StrictPlaneRow source9StrictPlaneColumn
    source9StrictPlaneEnumeration_ne (List.finRange 36)

/-- Full derivative of the actual natural matrix image of the chosen actual word. -/
theorem source9OrderedStrictPlaneWord_matrix_hasFDerivAt_zero :
    HasFDerivAt
      (fun t : Fin 36 → ℝ =>
        ((source9SpinVectorOrthogonalHom (source9OrderedStrictPlaneWord t)) :
          Matrix SpaceIndex SpaceIndex ℝ))
      (source9PlaneWordMatrixVelocity source9StrictPlaneRow source9StrictPlaneColumn
        (List.finRange 36)) 0 :=
  source9PlaneSpinWord_vectorOrthogonalMatrix_hasFDerivAt_zero
    source9StrictPlaneRow source9StrictPlaneColumn source9StrictPlaneEnumeration_ne
      (List.finRange 36)

/-- Every direction is the literal ordered sum, with full native-plane normalization. -/
theorem source9OrderedStrictPlaneWord_matrix_fderiv_zero_apply (v : Fin 36 → ℝ) :
    (fderiv ℝ
      (fun t : Fin 36 → ℝ =>
        ((source9SpinVectorOrthogonalHom (source9OrderedStrictPlaneWord t)) :
          Matrix SpaceIndex SpaceIndex ℝ)) 0) v =
      ((List.finRange 36).map (fun i =>
        v i • coordinatePlane9 (source9StrictPlaneRow i) (source9StrictPlaneColumn i))).sum :=
  source9PlaneSpinWord_vectorOrthogonalMatrix_fderiv_zero_apply
    source9StrictPlaneRow source9StrictPlaneColumn source9StrictPlaneEnumeration_ne
      (List.finRange 36) v

#print axioms source9StrictPlaneEnumeration
#print axioms source9StrictPlaneEnumeration_bijective
#print axioms source9StrictPlaneEnumeration_ne
#print axioms source9OrderedStrictPlaneWord
#print axioms source9OrderedStrictPlaneWord_zero
#print axioms source9OrderedStrictPlaneWord_matrix_hasFDerivAt_zero
#print axioms source9OrderedStrictPlaneWord_matrix_fderiv_zero_apply

end
end FCP.BFSSPairedSpin9Clifford
