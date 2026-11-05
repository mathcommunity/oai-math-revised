import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CJCoordinateReconstructionDomain
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! F10CK: polynomial completion coordinates on the original nine-matrix perturbation space.
On orthogonal matrices these coordinates depend only on the accepted strict upper entries.
No local injectivity, inverse-function conclusion or source Spin coverage is asserted here.
Candidate until complete strict source compilation and independent audit pass. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open scoped Matrix.Norms.Elementwise

/-- Identity linear part, with a lower-triangle quadratic Gram correction. -/
noncomputable def source9OrthogonalCompletionMap (B : Matrix SpaceIndex SpaceIndex ℝ) :
    Matrix SpaceIndex SpaceIndex ℝ := fun i j =>
  if i < j then B i j
  else if j < i then B i j + (B.transpose * B) i j
  else B i j + (B.transpose * B) i j / 2

theorem source9OrthogonalCompletionMap_zero : source9OrthogonalCompletionMap 0 = 0 := by
  funext i j
  simp [source9OrthogonalCompletionMap]

/-- Exact second-order Gram expansion about the identity in the original matrix carrier. -/
theorem source9Matrix_perturbation_gram_identity (B : Matrix SpaceIndex SpaceIndex ℝ) :
    (1 + B).transpose * (1 + B) - 1 = B + B.transpose + B.transpose * B := by
  simp only [Matrix.transpose_add, Matrix.transpose_one, add_mul, mul_add, one_mul, mul_one]
  abel

theorem source9Orthogonal_perturbation_gram_zero (A : Matrix SpaceIndex SpaceIndex ℝ)
    (hA : A ∈ Matrix.orthogonalGroup SpaceIndex ℝ) :
    (A - 1) + (A - 1).transpose + (A - 1).transpose * (A - 1) = 0 := by
  have h := source9Matrix_perturbation_gram_identity (A - 1)
  have heq : (1 : Matrix SpaceIndex SpaceIndex ℝ) + (A - 1) = A := by abel
  have horth : A.transpose * A = 1 :=
    (Matrix.mem_orthogonalGroup_iff' SpaceIndex ℝ).1 hA
  rw [heq, horth, sub_self] at h
  exact h.symm

private theorem completion_perturbation_offDiagonal (A : Matrix SpaceIndex SpaceIndex ℝ)
    (i j : SpaceIndex) (hij : i ≠ j) : (A - 1) i j = A i j := by
  change A i j - (1 : Matrix SpaceIndex SpaceIndex ℝ) i j = A i j
  rw [Matrix.one_apply, ite_eq_right hij, sub_zero]

/-- On an actual orthogonal matrix, completion is precisely the native upper-entry skew model. -/
theorem source9OrthogonalCompletionMap_on_orthogonal (A : Matrix SpaceIndex SpaceIndex ℝ)
    (hA : A ∈ Matrix.orthogonalGroup SpaceIndex ℝ) :
    source9OrthogonalCompletionMap (A - 1) =
      source9StrictPlaneMatrix (fun p : source9StrictPlaneIndex => A p.val.1 p.val.2) := by
  apply Matrix.ext
  intro i j
  have hg := congrArg (fun M : Matrix SpaceIndex SpaceIndex ℝ => M i j)
    (source9Orthogonal_perturbation_gram_zero A hA)
  change (A - 1) i j + (A - 1) j i + ((A - 1).transpose * (A - 1)) i j = 0 at hg
  by_cases hij : i < j
  · simp only [source9OrthogonalCompletionMap, ite_eq_left hij,
      source9StrictPlaneMatrix, dite_eq_left hij]
    exact completion_perturbation_offDiagonal A i j (ne_of_lt hij)
  · by_cases hji : j < i
    · simp only [source9OrthogonalCompletionMap, ite_eq_right hij, ite_eq_left hji,
        source9StrictPlaneMatrix, dite_eq_right hij, dite_eq_left hji]
      have hne : i ≠ j := ne_of_gt hji
      rw [completion_perturbation_offDiagonal A i j hne,
        completion_perturbation_offDiagonal A j i hne.symm] at hg
      rw [completion_perturbation_offDiagonal A i j hne]
      linarith
    · have heq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      subst j
      simp only [source9OrthogonalCompletionMap, ite_eq_right (lt_irrefl i),
        source9StrictPlaneMatrix, dite_eq_right (lt_irrefl i)]
      linarith

/-- The accepted enumeration recovers exactly every native strict upper entry. -/
theorem source9OrderedUpperProjection_eq_iff_strict_entries (A B : Matrix SpaceIndex SpaceIndex ℝ) :
    source9OrderedUpperProjection A = source9OrderedUpperProjection B ↔
      ∀ p : source9StrictPlaneIndex, A p.val.1 p.val.2 = B p.val.1 p.val.2 := by
  constructor
  · intro h p
    let k : Fin 36 := source9StrictPlaneEnumeration.symm p
    have hentry := (source9OrderedUpperProjection_apply A k).symm.trans
      ((congrFun h k).trans (source9OrderedUpperProjection_apply B k))
    change A (source9StrictPlaneEnumeration k).val.1 (source9StrictPlaneEnumeration k).val.2 =
      B (source9StrictPlaneEnumeration k).val.1 (source9StrictPlaneEnumeration k).val.2 at hentry
    have hk : source9StrictPlaneEnumeration k = p := source9StrictPlaneEnumeration.apply_symm_apply p
    rw [hk] at hentry
    exact hentry
  · intro h
    funext k
    have hentry : A (source9StrictPlaneRow k) (source9StrictPlaneColumn k) =
        B (source9StrictPlaneRow k) (source9StrictPlaneColumn k) := h (source9StrictPlaneEnumeration k)
    exact (source9OrderedUpperProjection_apply A k).trans
      (hentry.trans (source9OrderedUpperProjection_apply B k).symm)

theorem source9OrthogonalCompletionMap_eq_of_upperProjection_eq
    (A B : Matrix SpaceIndex SpaceIndex ℝ)
    (hA : A ∈ Matrix.orthogonalGroup SpaceIndex ℝ)
    (hB : B ∈ Matrix.orthogonalGroup SpaceIndex ℝ)
    (h : source9OrderedUpperProjection A = source9OrderedUpperProjection B) :
    source9OrthogonalCompletionMap (A - 1) = source9OrthogonalCompletionMap (B - 1) := by
  rw [source9OrthogonalCompletionMap_on_orthogonal A hA,
    source9OrthogonalCompletionMap_on_orthogonal B hB]
  apply congrArg source9StrictPlaneMatrix
  funext p
  exact (source9OrderedUpperProjection_eq_iff_strict_entries A B).1 h p

/-- Apply the algebraic bridge to the actual reconstructed and original natural matrices. -/
theorem source9OrthogonalCompletionMap_actual_reconstruction
    (g : spinGroup source9Quadratic) (hg : g ∈ source9SpinCoordinateReconstructionDomain) :
    source9OrthogonalCompletionMap
        (((source9SpinVectorOrthogonalHom (source9SpinCoordinateReconstruction g)) :
          Matrix SpaceIndex SpaceIndex ℝ) - 1) =
      source9OrthogonalCompletionMap
        (((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) - 1) := by
  have hc : source9OrderedUpperProjection
      ((source9SpinVectorOrthogonalHom (source9SpinCoordinateReconstruction g)) :
        Matrix SpaceIndex SpaceIndex ℝ) =
    source9OrderedUpperProjection
      ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) :=
    source9SpinCoordinateReconstruction_upperCoordinates g hg
  exact source9OrthogonalCompletionMap_eq_of_upperProjection_eq _ _
    (source9SpinVectorOrthogonalHom (source9SpinCoordinateReconstruction g)).property
    (source9SpinVectorOrthogonalHom g).property hc

#print axioms source9OrthogonalCompletionMap
#print axioms source9OrthogonalCompletionMap_zero
#print axioms source9Matrix_perturbation_gram_identity
#print axioms source9Orthogonal_perturbation_gram_zero
#print axioms source9OrthogonalCompletionMap_on_orthogonal
#print axioms source9OrderedUpperProjection_eq_iff_strict_entries
#print axioms source9OrthogonalCompletionMap_eq_of_upperProjection_eq
#print axioms source9OrthogonalCompletionMap_actual_reconstruction
end
end FCP.BFSSPairedSpin9Clifford
