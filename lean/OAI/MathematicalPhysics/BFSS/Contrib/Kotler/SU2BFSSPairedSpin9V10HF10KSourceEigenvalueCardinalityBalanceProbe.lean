import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10JSourceEigenvalueSignPartitionProbe
import Mathlib.Data.Finset.Card

/-!
K1D18V10H-F10K: source-exact original 16-gamma eigenvalue
multiplicity BALANCE, starting from qualified F10J's true
sign-filter partition and zero-trace source-spectral sum.

Four independent obligations:
* positive root sum = (positive card : Real) * sqrt(Q);
* negative root sum = (negative card : Real) * (-sqrt(Q));
* zero trace forces equality of real-cast cardinalities for v != 0;
* injection of Nat card casts gives exact Nat cardinality equality.

The exact 8/8 cardinality and the determinant's + sign are
NOT asserted by this bounded gate. They require an additional
original SpinIndex cardinality bridge and a product-sign argument.
No new matrices, private original gamma tables, altered paired-Fock
indexing or axioms, and no artificial resource-limit changes.
F10K candidate until fresh strict compilation and four independent
declaration type and axiom audits PASS.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9DetFixture
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9Clifford
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- In the ORIGINAL gamma positive-root filter, the
real eigenvalue sum is its exact cardinality times sqrt(Q). -/
theorem source9PositiveEigenIndices_sum_eq_card_mul_sqrt
    (v : SpaceIndex → ℝ) :
    (∑ i ∈ source9PositiveEigenIndices v,
      ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ)) =
    ((source9PositiveEigenIndices v).card : ℝ) *
      Real.sqrt (source9Quadratic v) := by
  classical
  calc
    (∑ i ∈ source9PositiveEigenIndices v,
      ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ)) =
      ∑ _i ∈ source9PositiveEigenIndices v,
        Real.sqrt (source9Quadratic v) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi' : i ∈ Finset.univ.filter
              (fun j : SpinIndex =>
                (gammaNineRealLinear_isHermitian v).eigenvalues j =
                  Real.sqrt (source9Quadratic v)) := by
            simpa only [source9PositiveEigenIndices] using hi
          exact (Finset.mem_filter.mp hi').2
    _ = ((source9PositiveEigenIndices v).card : ℝ) *
          Real.sqrt (source9Quadratic v) := by
          simp only [Finset.sum_const, nsmul_eq_mul]

/-- Same exact expression for the ORIGINAL negative-root filter. -/
theorem source9NegativeEigenIndices_sum_eq_card_mul_neg_sqrt
    (v : SpaceIndex → ℝ) :
    (∑ i ∈ source9NegativeEigenIndices v,
      ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ)) =
    ((source9NegativeEigenIndices v).card : ℝ) *
      (-Real.sqrt (source9Quadratic v)) := by
  classical
  calc
    (∑ i ∈ source9NegativeEigenIndices v,
      ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ)) =
      ∑ _i ∈ source9NegativeEigenIndices v,
        (-Real.sqrt (source9Quadratic v)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi' : i ∈ Finset.univ.filter
              (fun j : SpinIndex =>
                (gammaNineRealLinear_isHermitian v).eigenvalues j =
                  -Real.sqrt (source9Quadratic v)) := by
            simpa only [source9NegativeEigenIndices] using hi
          exact (Finset.mem_filter.mp hi').2
    _ = ((source9NegativeEigenIndices v).card : ℝ) *
          (-Real.sqrt (source9Quadratic v)) := by
          simp only [Finset.sum_const, nsmul_eq_mul]

/-- The exact source gamma trace zero and Q>0 imply
equal ORIGINAL positive and negative FILTER card casts. -/
theorem source9Eigenvalue_sign_card_cast_equal
    (v : SpaceIndex → ℝ) (hv : v ≠ 0) :
    ((source9PositiveEigenIndices v).card : ℝ) =
      ((source9NegativeEigenIndices v).card : ℝ) := by
  have htrace := source9Eigenvalue_sign_partition_sum_zero v hv
  rw [source9PositiveEigenIndices_sum_eq_card_mul_sqrt,
      source9NegativeEigenIndices_sum_eq_card_mul_neg_sqrt] at htrace
  have hdiff :
      (((source9PositiveEigenIndices v).card : ℝ) -
        ((source9NegativeEigenIndices v).card : ℝ)) *
          Real.sqrt (source9Quadratic v) = 0 := by
    calc
      (((source9PositiveEigenIndices v).card : ℝ) -
        ((source9NegativeEigenIndices v).card : ℝ)) *
          Real.sqrt (source9Quadratic v) =
        ((source9PositiveEigenIndices v).card : ℝ) *
          Real.sqrt (source9Quadratic v) +
        ((source9NegativeEigenIndices v).card : ℝ) *
          (-Real.sqrt (source9Quadratic v)) := by ring
      _ = 0 := htrace
  have hr : Real.sqrt (source9Quadratic v) ≠ 0 :=
    ne_of_gt (source9Quadratic_sqrt_pos_of_ne v hv)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_right hr)

/-- Equal real casts of Nat counts imply actual equality
of original sign-filter Nat cardinalities, not a proxy model. -/
theorem source9Eigenvalue_sign_card_equal
    (v : SpaceIndex → ℝ) (hv : v ≠ 0) :
    (source9PositiveEigenIndices v).card =
      (source9NegativeEigenIndices v).card := by
  exact_mod_cast source9Eigenvalue_sign_card_cast_equal v hv

#print axioms source9PositiveEigenIndices_sum_eq_card_mul_sqrt
#print axioms source9NegativeEigenIndices_sum_eq_card_mul_neg_sqrt
#print axioms source9Eigenvalue_sign_card_cast_equal
#print axioms source9Eigenvalue_sign_card_equal

end
end FCP.BFSSPairedSpin9DetFixture
