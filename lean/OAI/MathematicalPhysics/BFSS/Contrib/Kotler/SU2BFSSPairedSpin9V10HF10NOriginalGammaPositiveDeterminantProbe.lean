import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10MOriginalGammaEigenvalueProductPartitionProbe
import Mathlib.Tactic

/-!
K1D18V10H-F10N — exact ORIGINAL real gamma16 generator determinant sign.

Qualified original source ancestry:
F9: det Gamma(v) = ± source9Quadratic(v)^8, and the original Clifford
unit determinant maps the genuine source vector generator;
F10E: trace of original real gamma16 is zero;
F10F: original source quadratic positive-definite, original gamma symmetric;
F10G: det Gamma(v) equals product of its genuine real Hermitian eigenvalues;
F10H–F10L: original eigenvalues ±sqrt(Q), exactly eight of EACH sign;
F10M: both source-filter eigenvalue products and their full partition.

F10N separately tests exact gamma determinant sign for v != 0,
the universal statement including the v = 0 boundary, determinant
nonnegativity, and transfer of the universal positive determinant
formula to the accepted ORIGINAL Clifford unit-vector generator
homomorphism. No new private gamma table, basis permutation or
substitute representation. No global Spin9 orientation, SO48 action,
Spin48 lifting or BFSS physical spectrum is asserted.

All statements are candidate until a fresh pinned warningAsError
compilation and FOUR independent exact type/axiom checks pass.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9DetFixture
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9Clifford
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- Positive determinant branch for every NONZERO source
nine-vector in the exact original real 16-spinor gamma. -/
theorem gammaNineRealLinear_det_eq_source9Quadratic_pow8_of_ne
    (v : SpaceIndex → ℝ) (hv : v ≠ 0) :
    (gammaNineRealLinear v).det =
      (source9Quadratic v) ^ 8 := by
  calc
    (gammaNineRealLinear v).det =
        ∏ i : SpinIndex,
          ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ) :=
      gammaNineRealLinear_det_eq_realEigenvalues_prod v
    _ =
        (∏ i ∈ source9PositiveEigenIndices v,
          ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ)) *
        (∏ i ∈ source9NegativeEigenIndices v,
          ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ)) :=
      source9RealEigenvalue_prod_sign_partition v hv
    _ =
        (Real.sqrt (source9Quadratic v)) ^ 8 *
        (-Real.sqrt (source9Quadratic v)) ^ 8 := by
      rw [source9PositiveEigenIndices_prod_eq_sqrt_pow_eight v hv,
          source9NegativeEigenIndices_prod_eq_neg_sqrt_pow_eight v hv]
    _ = (Real.sqrt (source9Quadratic v) *
          Real.sqrt (source9Quadratic v)) ^ 8 := by ring
    _ = (source9Quadratic v) ^ 8 := by
      rw [Real.mul_self_sqrt (source9Quadratic_nonneg v)]

/-- The universal POSITIVE-branch determinant formula
for every original real source vector, including v=0.
The zero case uses the independently accepted original F9
two-sign determinant formula, whose branches coincide at Q=0. -/
theorem gammaNineRealLinear_det_eq_source9Quadratic_pow8
    (v : SpaceIndex → ℝ) :
    (gammaNineRealLinear v).det =
      (source9Quadratic v) ^ 8 := by
  by_cases hv : v = 0
  · subst v
    have hQ : source9Quadratic (0 : SpaceIndex → ℝ) = 0 := by
      rw [source9Quadratic_eq_dot]
      simp
    rcases gammaNineRealLinear_det_eq_pow8_or_neg (0 : SpaceIndex → ℝ) with h | h
    · exact h
    · simp [hQ] at h ⊢
  · exact gammaNineRealLinear_det_eq_source9Quadratic_pow8_of_ne v hv

/-- Every original source real gamma16 generator determinant
is nonnegative. This is not a global Spin9-character result. -/
theorem gammaNineRealLinear_det_nonneg
    (v : SpaceIndex → ℝ) :
    0 ≤ (gammaNineRealLinear v).det := by
  rw [gammaNineRealLinear_det_eq_source9Quadratic_pow8]
  exact pow_nonneg (source9Quadratic_nonneg v) 8

/-- The ACTUAL accepted original Clifford-unit determinant hom
chooses the positive branch on every genuine source vector unit.
This does NOT assert positive determinant on every Spin9 element
or a surjectivity/covering theorem for Spin48. -/
theorem source9CliffordUnitsGammaDetHom_generator_positive_branch
    (u : (CliffordAlgebra source9Quadratic)ˣ)
    (v : SpaceIndex → ℝ)
    (hvec : (u : CliffordAlgebra source9Quadratic) =
      CliffordAlgebra.ι source9Quadratic v) :
    source9CliffordUnitsGammaDetHom u =
      (source9Quadratic v) ^ 8 := by
  rw [source9CliffordUnitsGammaDetHom_generator u v hvec]
  exact gammaNineRealLinear_det_eq_source9Quadratic_pow8 v

#print axioms gammaNineRealLinear_det_eq_source9Quadratic_pow8_of_ne
#print axioms gammaNineRealLinear_det_eq_source9Quadratic_pow8
#print axioms gammaNineRealLinear_det_nonneg
#print axioms source9CliffordUnitsGammaDetHom_generator_positive_branch

end
end FCP.BFSSPairedSpin9DetFixture
