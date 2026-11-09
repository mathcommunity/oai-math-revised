import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CBOrderedStrictPlaneWord
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Fin

/-! F10CC: reindex the actual ordered-word derivative into canonical native so(9).
Algebraic model and coordinate recovery only. Continuity of the equivalence,
charts, tangent identifications and source local fiber control remain open.
Candidate until strict source and independent audit pass. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open FCP.BFSSPairedSpin9Plane
open scoped BigOperators Matrix.Norms.Elementwise

/-- Transport parameter coordinates through the already chosen native enumeration. -/
noncomputable def source9StrictPlaneParameterEquiv :
    (Fin 36 → ℝ) ≃ₗ[ℝ] (source9StrictPlaneIndex → ℝ) :=
  LinearEquiv.piCongrLeft' ℝ (fun _ : Fin 36 => ℝ) source9StrictPlaneEnumeration

theorem source9StrictPlaneParameterEquiv_apply (v : Fin 36 → ℝ)
    (p : source9StrictPlaneIndex) :
    source9StrictPlaneParameterEquiv v p = v (source9StrictPlaneEnumeration.symm p) := rfl

/-- The actual parameter model, with canonical native skew-matrix codomain. -/
noncomputable def source9OrderedStrictPlaneModelEquiv :
    (Fin 36 → ℝ) ≃ₗ[ℝ] LieAlgebra.Orthogonal.so SpaceIndex ℝ :=
  source9StrictPlaneParameterEquiv.trans source9StrictPlaneModelEquiv

/-- The ordered list sum is the underlying matrix of the canonical model. -/
theorem source9OrderedStrictPlane_sum_eq_model (v : Fin 36 → ℝ) :
    ((List.finRange 36).map (fun i =>
      v i • coordinatePlane9 (source9StrictPlaneRow i) (source9StrictPlaneColumn i))).sum =
      (source9OrderedStrictPlaneModelEquiv v : Matrix SpaceIndex SpaceIndex ℝ) := by
  change ((List.finRange 36).map (fun i =>
    v i • coordinatePlane9 (source9StrictPlaneRow i) (source9StrictPlaneColumn i))).sum =
      (source9StrictPlaneModelEquiv (source9StrictPlaneParameterEquiv v) :
        Matrix SpaceIndex SpaceIndex ℝ)
  rw [← Fin.sum_univ_def, source9StrictPlaneModelEquiv_apply_sum]
  apply Fintype.sum_equiv source9StrictPlaneEnumeration
  intro i
  simp only [source9StrictPlaneParameterEquiv_apply, Equiv.symm_apply_apply,
    source9StrictPlaneRow, source9StrictPlaneColumn]

/-- The actual entire natural-matrix derivative equals the canonical model in every direction. -/
theorem source9OrderedStrictPlaneWord_matrix_fderiv_zero_model (v : Fin 36 → ℝ) :
    (fderiv ℝ (fun t : Fin 36 → ℝ =>
      ((source9SpinVectorOrthogonalHom (source9OrderedStrictPlaneWord t)) :
        Matrix SpaceIndex SpaceIndex ℝ)) 0) v =
      (source9OrderedStrictPlaneModelEquiv v : Matrix SpaceIndex SpaceIndex ℝ) :=
  (source9OrderedStrictPlaneWord_matrix_fderiv_zero_apply v).trans
    (source9OrderedStrictPlane_sum_eq_model v)

/-- Original enumerated upper entries recover each actual input direction coordinate. -/
theorem source9OrderedStrictPlaneWord_matrix_fderiv_zero_upper
    (v : Fin 36 → ℝ) (i : Fin 36) :
    ((fderiv ℝ (fun t : Fin 36 → ℝ =>
      ((source9SpinVectorOrthogonalHom (source9OrderedStrictPlaneWord t)) :
        Matrix SpaceIndex SpaceIndex ℝ)) 0) v)
      (source9StrictPlaneRow i) (source9StrictPlaneColumn i) = v i := by
  rw [source9OrderedStrictPlaneWord_matrix_fderiv_zero_model]
  change (source9StrictPlaneModelEquiv (source9StrictPlaneParameterEquiv v)).val
    (source9StrictPlaneEnumeration i).val.1 (source9StrictPlaneEnumeration i).val.2 = v i
  have h := congrFun
    (source9StrictPlaneModelEquiv.symm_apply_apply (source9StrictPlaneParameterEquiv v))
    (source9StrictPlaneEnumeration i)
  change (source9StrictPlaneModelEquiv (source9StrictPlaneParameterEquiv v)).val
    (source9StrictPlaneEnumeration i).val.1 (source9StrictPlaneEnumeration i).val.2 =
      source9StrictPlaneParameterEquiv v (source9StrictPlaneEnumeration i) at h
  exact h.trans (by
    simp only [source9StrictPlaneParameterEquiv_apply, Equiv.symm_apply_apply])

/-- The actual derivative into the original matrix space is injective. -/
theorem source9OrderedStrictPlaneWord_matrix_fderiv_zero_injective :
    Function.Injective (fun v : Fin 36 → ℝ =>
      (fderiv ℝ (fun t : Fin 36 → ℝ =>
        ((source9SpinVectorOrthogonalHom (source9OrderedStrictPlaneWord t)) :
          Matrix SpaceIndex SpaceIndex ℝ)) 0) v) := by
  intro v w h
  funext i
  have hi := congrArg (fun A : Matrix SpaceIndex SpaceIndex ℝ =>
    A (source9StrictPlaneRow i) (source9StrictPlaneColumn i)) h
  exact (source9OrderedStrictPlaneWord_matrix_fderiv_zero_upper v i).symm.trans
    (hi.trans (source9OrderedStrictPlaneWord_matrix_fderiv_zero_upper w i))

#print axioms source9StrictPlaneParameterEquiv
#print axioms source9StrictPlaneParameterEquiv_apply
#print axioms source9OrderedStrictPlaneModelEquiv
#print axioms source9OrderedStrictPlane_sum_eq_model
#print axioms source9OrderedStrictPlaneWord_matrix_fderiv_zero_model
#print axioms source9OrderedStrictPlaneWord_matrix_fderiv_zero_upper
#print axioms source9OrderedStrictPlaneWord_matrix_fderiv_zero_injective
end
end FCP.BFSSPairedSpin9Clifford
