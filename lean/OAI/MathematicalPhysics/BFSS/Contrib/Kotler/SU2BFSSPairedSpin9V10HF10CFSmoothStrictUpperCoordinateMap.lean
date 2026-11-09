import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CEUpperCoordinateIdentityDerivative
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! F10CF: smooth actual upper-coordinate map and strict identity derivative.
Reuse actual word-action smoothness and original coordinate columns.
No parameter-space inverse, subgroup chart, source coverage or local kernel
theorem is supplied here. Candidate until complete strict CI succeeds. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open scoped ContDiff Matrix.Norms.Elementwise

/-- Original coordinate-column entry bridge for the actual natural homomorphism. -/
theorem source9NaturalMatrix_entry_eq_vectorConjugation
    (g : spinGroup source9Quadratic) (i j : SpaceIndex) :
    ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) i j =
      source9SpinVectorConjugation g (source9CoordinateVector j) i := rfl

/-- The actual ordered word acts smoothly on every fixed original coordinate vector. -/
theorem source9OrderedStrictPlaneWord_column_contDiff (n : ℕ∞ω) (j : SpaceIndex) :
    ContDiff ℝ n (fun t : Fin 36 → ℝ =>
      source9SpinVectorConjugation (source9OrderedStrictPlaneWord t)
        (source9CoordinateVector j)) := by
  have hpair : ContDiff ℝ n (fun t : Fin 36 → ℝ => (t, source9CoordinateVector j)) :=
    contDiff_id.prodMk contDiff_const
  have h := (source9PlaneSpinWord_vectorAction_contDiff_pbw n
    source9StrictPlaneRow source9StrictPlaneColumn source9StrictPlaneEnumeration_ne
      (List.finRange 36)).comp hpair
  change ContDiff ℝ n (fun t : Fin 36 → ℝ =>
    source9SpinVectorConjugation (source9OrderedStrictPlaneWord t)
      (source9CoordinateVector j)) at h
  exact h

/-- Every entry of the entire actual natural matrix word map is smooth. -/
theorem source9OrderedStrictPlaneWord_matrix_entry_contDiff
    (n : ℕ∞ω) (i j : SpaceIndex) :
    ContDiff ℝ n (fun t : Fin 36 → ℝ =>
      ((source9SpinVectorOrthogonalHom (source9OrderedStrictPlaneWord t)) :
        Matrix SpaceIndex SpaceIndex ℝ) i j) := by
  have h := (contDiff_apply ℝ ℝ i).comp
    (source9OrderedStrictPlaneWord_column_contDiff n j)
  change ContDiff ℝ n (fun t : Fin 36 → ℝ =>
    source9SpinVectorConjugation (source9OrderedStrictPlaneWord t)
      (source9CoordinateVector j) i) at h
  have heq :
      (fun t : Fin 36 → ℝ =>
        ((source9SpinVectorOrthogonalHom (source9OrderedStrictPlaneWord t)) :
          Matrix SpaceIndex SpaceIndex ℝ) i j) =
      (fun t : Fin 36 → ℝ =>
        source9SpinVectorConjugation (source9OrderedStrictPlaneWord t)
          (source9CoordinateVector j) i) := by
    funext t
    exact source9NaturalMatrix_entry_eq_vectorConjugation
      (source9OrderedStrictPlaneWord t) i j
  rw [← heq] at h
  exact h

/-- Smoothness of the complete underlying actual natural matrix word image. -/
theorem source9OrderedStrictPlaneWord_matrix_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (fun t : Fin 36 → ℝ =>
      ((source9SpinVectorOrthogonalHom (source9OrderedStrictPlaneWord t)) :
        Matrix SpaceIndex SpaceIndex ℝ)) := by
  apply contDiff_pi.2
  intro i
  apply contDiff_pi.2
  intro j
  exact source9OrderedStrictPlaneWord_matrix_entry_contDiff n i j

/-- The exact accepted upper-coordinate map is smooth at every order. -/
theorem source9OrderedUpperCoordinateMap_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n source9OrderedUpperCoordinateMap := by
  have h := source9OrderedUpperProjection.contDiff.comp
    (source9OrderedStrictPlaneWord_matrix_contDiff n)
  change ContDiff ℝ n source9OrderedUpperCoordinateMap at h
  exact h

theorem source9OrderedUpperCoordinateMap_contDiffAt_one_zero :
    ContDiffAt ℝ (1 : ℕ∞ω) source9OrderedUpperCoordinateMap 0 :=
  (source9OrderedUpperCoordinateMap_contDiff (1 : ℕ∞ω)).contDiffAt

/-- The accepted ordinary identity derivative is a strict derivative of the actual map. -/
theorem source9OrderedUpperCoordinateMap_hasStrictFDerivAt_zero :
    HasStrictFDerivAt source9OrderedUpperCoordinateMap
      (ContinuousLinearMap.id ℝ (Fin 36 → ℝ)) 0 :=
  source9OrderedUpperCoordinateMap_contDiffAt_one_zero.hasStrictFDerivAt'
    source9OrderedUpperCoordinateMap_hasFDerivAt_zero one_ne_zero

#print axioms source9NaturalMatrix_entry_eq_vectorConjugation
#print axioms source9OrderedStrictPlaneWord_column_contDiff
#print axioms source9OrderedStrictPlaneWord_matrix_entry_contDiff
#print axioms source9OrderedStrictPlaneWord_matrix_contDiff
#print axioms source9OrderedUpperCoordinateMap_contDiff
#print axioms source9OrderedUpperCoordinateMap_contDiffAt_one_zero
#print axioms source9OrderedUpperCoordinateMap_hasStrictFDerivAt_zero
end
end FCP.BFSSPairedSpin9Clifford
