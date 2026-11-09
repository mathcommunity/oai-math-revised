import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BYActualWordVectorActionDerivative
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BRSourceVectorOrthogonalHom
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Matrix.Normed

/-!
F10BZ — full ambient derivative of the entire natural nine-matrix word action.

Candidate only until fresh strict compilation and independent topology/type/axiom
audit. Assemble the accepted fixed-vector action derivatives on the original
coordinate columns. The matrix norm is the standard elementwise norm, with
its product topology checked independently.

The derivative is the literal listed sum of full native coordinate planes.
This is a finite-parameter ordinary matrix-space derivative. It supplies no
subgroup atlas, selected invertible model, tangent identification, covering
or full F10BC manifold differential.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSPairedSpin9Plane
open scoped Matrix.Norms.Elementwise

/-- The matrix derivative, assembled from exact vector-action coordinate columns. -/
noncomputable def source9PlaneWordMatrixVelocity {k : ℕ}
    (r s : Fin k → SpaceIndex) (l : List (Fin k)) :
    (Fin k → ℝ) →L[ℝ] Matrix SpaceIndex SpaceIndex ℝ :=
  ContinuousLinearMap.pi (fun i : SpaceIndex =>
    ContinuousLinearMap.pi (fun j : SpaceIndex =>
      (ContinuousLinearMap.proj i : (SpaceIndex → ℝ) →L[ℝ] ℝ).comp
        (source9PlaneWordVectorVelocity r s (source9CoordinateVector j) l)))

/-- Its value in every direction is the literal finite sum of full native matrices. -/
theorem source9PlaneWordMatrixVelocity_apply {k : ℕ}
    (r s : Fin k → SpaceIndex) (l : List (Fin k)) (v : Fin k → ℝ) :
    source9PlaneWordMatrixVelocity r s l v =
      (l.map (fun a => v a • coordinatePlane9 (r a) (s a))).sum := by
  induction l with
  | nil =>
      apply Matrix.ext
      intro i j
      rfl
  | cons a l ih =>
      apply Matrix.ext
      intro i j
      have hcolumn :
          ((coordinatePlane9 (r a) (s a)).mulVec (source9CoordinateVector j)) i =
            coordinatePlane9 (r a) (s a) i j := by
        change dotProduct ((coordinatePlane9 (r a) (s a)) i) (Pi.single j (1 : ℝ)) =
          coordinatePlane9 (r a) (s a) i j
        rw [dotProduct_single, mul_one]
      have htail :
          source9PlaneWordVectorVelocity r s (source9CoordinateVector j) l v i =
            ((l.map (fun b => v b • coordinatePlane9 (r b) (s b))).sum) i j :=
        congrArg (fun A : Matrix SpaceIndex SpaceIndex ℝ => A i j) ih
      simp only [List.map_cons, List.sum_cons]
      change
        v a * (((coordinatePlane9 (r a) (s a)).mulVec (source9CoordinateVector j)) i) +
          source9PlaneWordVectorVelocity r s (source9CoordinateVector j) l v i =
        v a * coordinatePlane9 (r a) (s a) i j +
          ((l.map (fun b => v b • coordinatePlane9 (r b) (s b))).sum) i j
      rw [hcolumn, htail]

/-- Each exact natural matrix entry has the full finite-parameter column derivative. -/
theorem source9PlaneSpinWord_vectorMatrix_entry_hasFDerivAt_zero {k : ℕ}
    (r s : Fin k → SpaceIndex) (hrs : ∀ a, r a ≠ s a)
    (l : List (Fin k)) (i j : SpaceIndex) :
    HasFDerivAt
      (fun t : Fin k → ℝ => source9SpinVectorMatrixHom (source9PlaneSpinWord r s hrs t l) i j)
      ((ContinuousLinearMap.proj i : (SpaceIndex → ℝ) →L[ℝ] ℝ).comp
        (source9PlaneWordVectorVelocity r s (source9CoordinateVector j) l)) 0 := by
  have hcol := source9PlaneSpinWord_vectorAction_hasFDerivAt_zero
    r s hrs l (source9CoordinateVector j)
  have hi := (hasFDerivAt_pi'.1 hcol) i
  have heq :
      (fun t : Fin k → ℝ =>
        source9SpinVectorMatrixHom (source9PlaneSpinWord r s hrs t l) i j) =
      (fun t : Fin k → ℝ =>
        source9SpinVectorConjugation (source9PlaneSpinWord r s hrs t l)
          (source9CoordinateVector j) i) := by
    funext t
    rfl
  rw [← heq] at hi
  exact hi

/-- The whole actual natural orthogonal image matrix has the exact full derivative at zero. -/
theorem source9PlaneSpinWord_vectorOrthogonalMatrix_hasFDerivAt_zero {k : ℕ}
    (r s : Fin k → SpaceIndex) (hrs : ∀ a, r a ≠ s a) (l : List (Fin k)) :
    HasFDerivAt
      (fun t : Fin k → ℝ =>
        ((source9SpinVectorOrthogonalHom (source9PlaneSpinWord r s hrs t l)) :
          Matrix SpaceIndex SpaceIndex ℝ))
      (source9PlaneWordMatrixVelocity r s l) 0 := by
  change HasFDerivAt
    (fun t : Fin k → ℝ => fun i j =>
      source9SpinVectorMatrixHom (source9PlaneSpinWord r s hrs t l) i j)
    (ContinuousLinearMap.pi (fun i : SpaceIndex =>
      ContinuousLinearMap.pi (fun j : SpaceIndex =>
        (ContinuousLinearMap.proj i : (SpaceIndex → ℝ) →L[ℝ] ℝ).comp
          (source9PlaneWordVectorVelocity r s (source9CoordinateVector j) l)))) 0
  apply hasFDerivAt_pi.2
  intro i
  apply hasFDerivAt_pi.2
  intro j
  exact source9PlaneSpinWord_vectorMatrix_entry_hasFDerivAt_zero r s hrs l i j

/-- The literal whole natural matrix fderiv is the exact assembled continuous linear map. -/
theorem source9PlaneSpinWord_vectorOrthogonalMatrix_fderiv_zero {k : ℕ}
    (r s : Fin k → SpaceIndex) (hrs : ∀ a, r a ≠ s a) (l : List (Fin k)) :
    fderiv ℝ
      (fun t : Fin k → ℝ =>
        ((source9SpinVectorOrthogonalHom (source9PlaneSpinWord r s hrs t l)) :
          Matrix SpaceIndex SpaceIndex ℝ)) 0 =
      source9PlaneWordMatrixVelocity r s l :=
  (source9PlaneSpinWord_vectorOrthogonalMatrix_hasFDerivAt_zero r s hrs l).fderiv

/-- In every direction, the actual whole-matrix derivative is the literal full native-plane sum. -/
theorem source9PlaneSpinWord_vectorOrthogonalMatrix_fderiv_zero_apply {k : ℕ}
    (r s : Fin k → SpaceIndex) (hrs : ∀ a, r a ≠ s a)
    (l : List (Fin k)) (v : Fin k → ℝ) :
    (fderiv ℝ
      (fun t : Fin k → ℝ =>
        ((source9SpinVectorOrthogonalHom (source9PlaneSpinWord r s hrs t l)) :
          Matrix SpaceIndex SpaceIndex ℝ)) 0) v =
      (l.map (fun a => v a • coordinatePlane9 (r a) (s a))).sum := by
  have hmap :
      fderiv ℝ
        (fun t : Fin k → ℝ =>
          ((source9SpinVectorOrthogonalHom (source9PlaneSpinWord r s hrs t l)) :
            Matrix SpaceIndex SpaceIndex ℝ)) 0 =
      source9PlaneWordMatrixVelocity r s l :=
    source9PlaneSpinWord_vectorOrthogonalMatrix_fderiv_zero r s hrs l
  exact (congrArg
    (fun L : (Fin k → ℝ) →L[ℝ] Matrix SpaceIndex SpaceIndex ℝ => L v) hmap).trans
      (source9PlaneWordMatrixVelocity_apply r s l v)

#print axioms source9PlaneWordMatrixVelocity
#print axioms source9PlaneWordMatrixVelocity_apply
#print axioms source9PlaneSpinWord_vectorMatrix_entry_hasFDerivAt_zero
#print axioms source9PlaneSpinWord_vectorOrthogonalMatrix_hasFDerivAt_zero
#print axioms source9PlaneSpinWord_vectorOrthogonalMatrix_fderiv_zero
#print axioms source9PlaneSpinWord_vectorOrthogonalMatrix_fderiv_zero_apply

end
end FCP.BFSSPairedSpin9Clifford
