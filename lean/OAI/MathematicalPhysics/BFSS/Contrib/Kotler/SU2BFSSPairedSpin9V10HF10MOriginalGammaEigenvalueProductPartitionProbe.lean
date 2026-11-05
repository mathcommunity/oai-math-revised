import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10LSourceRealEigenvalueEightEachProbe
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
K1D18V10H-F10M — original source real gamma16 eigenvalue PRODUCTS.

F10L strictly qualified exactly eight real eigenvalues in each of
the two ACTUAL source spectral sign classes, indexed by SpinIndex := Fin 16.
The original F10G determinant is the product of its ACTUAL eigenvalues.
Before selecting any determinant sign, qualify these three source-exact
finite-product bridges separately:

* positive sign-filter real eigenvalue product = sqrt(Q)^8;
* negative sign-filter product = (-sqrt(Q))^8;
* full original 16-index real eigenvalue product equals
  positive filter product times negative filter product, v!=0.

All proofs use the original spectral eigenvalues and exact source
filters; no private gamma signed-permutation table, surrogate matrix,
invented original Spin9 invariance, assumed determinant sign or Fock
index permutation. No additional axioms or resource-limit changes.
F10M is UNQUALIFIED until strict warning-as-error compilation and
independent exact types/root axiom audits PASS.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9DetFixture
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9Clifford
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- Exactly eight original real gamma eigenvalues are the
positive root, hence their exact filter product is sqrt(Q)^8. -/
theorem source9PositiveEigenIndices_prod_eq_sqrt_pow_eight
    (v : SpaceIndex → ℝ) (hv : v ≠ 0) :
    (∏ i ∈ source9PositiveEigenIndices v,
      ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ)) =
    (Real.sqrt (source9Quadratic v)) ^ 8 := by
  classical
  have hprod :
      (∏ i ∈ source9PositiveEigenIndices v,
        ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ)) =
        (Real.sqrt (source9Quadratic v)) ^
          (source9PositiveEigenIndices v).card := by
    apply Finset.prod_eq_pow_card
    intro i hi
    have hi' : i ∈ Finset.univ.filter
        (fun j : SpinIndex =>
          (gammaNineRealLinear_isHermitian v).eigenvalues j =
            Real.sqrt (source9Quadratic v)) := by
      simpa only [source9PositiveEigenIndices] using hi
    exact (Finset.mem_filter.mp hi').2
  rw [hprod, source9PositiveEigenIndices_card_eight v hv]

/-- Exactly eight original real gamma eigenvalues are the
negative root, hence their product is (-sqrt(Q))^8. -/
theorem source9NegativeEigenIndices_prod_eq_neg_sqrt_pow_eight
    (v : SpaceIndex → ℝ) (hv : v ≠ 0) :
    (∏ i ∈ source9NegativeEigenIndices v,
      ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ)) =
    (-Real.sqrt (source9Quadratic v)) ^ 8 := by
  classical
  have hprod :
      (∏ i ∈ source9NegativeEigenIndices v,
        ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ)) =
        (-Real.sqrt (source9Quadratic v)) ^
          (source9NegativeEigenIndices v).card := by
    apply Finset.prod_eq_pow_card
    intro i hi
    have hi' : i ∈ Finset.univ.filter
        (fun j : SpinIndex =>
          (gammaNineRealLinear_isHermitian v).eigenvalues j =
            -Real.sqrt (source9Quadratic v)) := by
      simpa only [source9NegativeEigenIndices] using hi
    exact (Finset.mem_filter.mp hi').2
  rw [hprod, source9NegativeEigenIndices_card_eight v hv]

/-- The product of ALL original real gamma16 eigenvalues
splits into the exact two actual source spectral filter
products; source F10J proves that negative means not positive. -/
theorem source9RealEigenvalue_prod_sign_partition
    (v : SpaceIndex → ℝ) (hv : v ≠ 0) :
    (∏ i : SpinIndex,
      ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ)) =
    (∏ i ∈ source9PositiveEigenIndices v,
      ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ)) *
    (∏ i ∈ source9NegativeEigenIndices v,
      ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ)) := by
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
  exact (Finset.prod_filter_mul_prod_filter_not
    (s := (Finset.univ : Finset SpinIndex))
    (p := fun i : SpinIndex =>
      (gammaNineRealLinear_isHermitian v).eigenvalues i =
        Real.sqrt (source9Quadratic v))
    (f := fun i : SpinIndex =>
      ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ))).symm

#print axioms source9PositiveEigenIndices_prod_eq_sqrt_pow_eight
#print axioms source9NegativeEigenIndices_prod_eq_neg_sqrt_pow_eight
#print axioms source9RealEigenvalue_prod_sign_partition

end
end FCP.BFSSPairedSpin9DetFixture
