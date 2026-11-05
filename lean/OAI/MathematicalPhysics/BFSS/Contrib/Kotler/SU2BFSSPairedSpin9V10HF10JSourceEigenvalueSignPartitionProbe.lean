import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10IRealEigenvalueSqrtTwoSignProbe
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter

/-!
K1D18V10H-F10J — FINITE ORIGINAL 16-spinor source eigenvalue sign partition.

F10I is qualified. At nonzero source v, its real spectrum is +sqrt(Q)
or -sqrt(Q) with strictly positive sqrt. Before claiming eight/eight
multiplicities, prove the exact set partition and zero trace split
on the ORIGINAL source SpinIndex, using pinned Mathlib finite filters.

1. A negative eigenvalue iff it is NOT the positive root.
2. Positive/negative filter cardinalities sum to Fintype.card SpinIndex.
3. The original zero-trace spectral sum splits between those filters.

No eigenvalue count 8/8 or positive determinant asserted by this gate.
No substitute representation, private signed permutation, or change to
the source paired-Fock indexing. Source-exact qualification required.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9DetFixture
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9Clifford
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- Exact positive-root eigenvalue indices of the
ORIGINAL 16-real-spinor gamma on an original nine-vector. -/
noncomputable def source9PositiveEigenIndices
    (v : SpaceIndex → ℝ) : Finset SpinIndex := by
  classical
  exact Finset.univ.filter
    (fun i : SpinIndex =>
      (gammaNineRealLinear_isHermitian v).eigenvalues i =
        Real.sqrt (source9Quadratic v))

/-- Exact negative-root eigenvalue indices of the
ORIGINAL gamma spectral function (not the complement by definition). -/
noncomputable def source9NegativeEigenIndices
    (v : SpaceIndex → ℝ) : Finset SpinIndex := by
  classical
  exact Finset.univ.filter
    (fun i : SpinIndex =>
      (gammaNineRealLinear_isHermitian v).eigenvalues i =
        -Real.sqrt (source9Quadratic v))

/-- Strict positivity of the original Q excludes overlap
of +sqrt(Q) and -sqrt(Q), with F10I providing coverage. -/
theorem source9RealEigenvalue_negative_iff_not_positive
    (v : SpaceIndex → ℝ) (hv : v ≠ 0) (i : SpinIndex) :
    ((gammaNineRealLinear_isHermitian v).eigenvalues i =
        -Real.sqrt (source9Quadratic v)) ↔
      ¬ ((gammaNineRealLinear_isHermitian v).eigenvalues i =
        Real.sqrt (source9Quadratic v)) := by
  constructor
  · intro hn hp
    have hpos := source9Quadratic_sqrt_pos_of_ne v hv
    have hcontra :
        -Real.sqrt (source9Quadratic v) =
          Real.sqrt (source9Quadratic v) := hn.symm.trans hp
    linarith
  · intro hnot
    exact (gammaNineRealLinear_realEigenvalues_eq_sqrt_or_neg v i).resolve_left hnot

/-- The positive and negative original gamma eigenvalue-index
classes partition ALL the actual source SpinIndex labels. -/
theorem source9Eigenvalue_sign_partition_card
    (v : SpaceIndex → ℝ) (hv : v ≠ 0) :
    (source9PositiveEigenIndices v).card +
      (source9NegativeEigenIndices v).card =
        Fintype.card SpinIndex := by
  classical
  have hneg :
      source9NegativeEigenIndices v =
        Finset.univ.filter
          (fun i : SpinIndex =>
            ¬ ((gammaNineRealLinear_isHermitian v).eigenvalues i =
              Real.sqrt (source9Quadratic v))) := by
    unfold source9NegativeEigenIndices
    apply Finset.filter_congr
    intro i hi
    exact source9RealEigenvalue_negative_iff_not_positive v hv i
  rw [hneg]
  unfold source9PositiveEigenIndices
  simpa only [Finset.card_univ] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset SpinIndex))
      (p := fun i : SpinIndex =>
        (gammaNineRealLinear_isHermitian v).eigenvalues i =
          Real.sqrt (source9Quadratic v)))

/-- Zero trace of the ORIGINAL source gamma, split
into its two exact source-eigenvalue sign classes. -/
theorem source9Eigenvalue_sign_partition_sum_zero
    (v : SpaceIndex → ℝ) (hv : v ≠ 0) :
    (∑ i ∈ source9PositiveEigenIndices v,
       ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ)) +
    (∑ i ∈ source9NegativeEigenIndices v,
       ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ)) = 0 := by
  classical
  have hneg :
      source9NegativeEigenIndices v =
        Finset.univ.filter
          (fun i : SpinIndex =>
            ¬ ((gammaNineRealLinear_isHermitian v).eigenvalues i =
              Real.sqrt (source9Quadratic v))) := by
    unfold source9NegativeEigenIndices
    apply Finset.filter_congr
    intro i hi
    exact source9RealEigenvalue_negative_iff_not_positive v hv i
  rw [hneg]
  unfold source9PositiveEigenIndices
  calc
    (∑ i ∈ (Finset.univ.filter
        (fun i : SpinIndex =>
          (gammaNineRealLinear_isHermitian v).eigenvalues i =
            Real.sqrt (source9Quadratic v))),
        ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ)) +
      (∑ i ∈ (Finset.univ.filter
        (fun i : SpinIndex =>
          ¬ ((gammaNineRealLinear_isHermitian v).eigenvalues i =
            Real.sqrt (source9Quadratic v)))),
        ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ)) =
      ∑ i : SpinIndex,
        ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ) := by
          exact Finset.sum_filter_add_sum_filter_not _ _ _
    _ = 0 := gammaNineRealLinear_realEigenvalues_sum_zero v

#print axioms source9RealEigenvalue_negative_iff_not_positive
#print axioms source9Eigenvalue_sign_partition_card
#print axioms source9Eigenvalue_sign_partition_sum_zero

end
end FCP.BFSSPairedSpin9DetFixture
