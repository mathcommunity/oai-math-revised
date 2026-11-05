import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9LinearMapImageSkewProbe
import Mathlib.Data.Matrix.Basis

/-!
K1D18V9D — exact native nine-index skew-input entry bridge and
finite matrix-unit decomposition. These are prerequisites for
an arbitrary skew-input coordinate-plane spanning theorem.

The input type remains Matrix SpaceIndex SpaceIndex ℝ; the output
of the previously accepted map is on original paired 48-real labels.
No basis permutation or external Lie homomorphism is assumed.

This stage uses the pinned Mathlib Matrix.matrix_eq_sum_single rather
than inventing a new finite-dimensional matrix decomposition.
Full skew coordinate-plane spanning, arbitrary bracket preservation,
and any global Spin(9) lift remain separate unproved obligations.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open scoped BigOperators

/-- Transpose-negation means entrywise antisymmetry on source-native
nine spatial labels, including diagonal pairs. -/
theorem coordinateSkewInput_entry
    (A : Matrix SpaceIndex SpaceIndex ℝ)
    (hA : A.transpose = -A) (r s : SpaceIndex) :
    A s r = -(A r s) := by
  exact congrArg (fun X : Matrix SpaceIndex SpaceIndex ℝ => X r s) hA

/-- Every source-native real nine-index matrix is the exact finite
sum of its scalar coefficients times pinned matrix units. -/
theorem coordinateMatrix9_coefficients_on_units
    (A : Matrix SpaceIndex SpaceIndex ℝ) :
    A = ∑ r : SpaceIndex, ∑ s : SpaceIndex,
      (A r s) • (Matrix.single r s (1 : ℝ) :
        Matrix SpaceIndex SpaceIndex ℝ) := by
  calc
    A = ∑ r : SpaceIndex, ∑ s : SpaceIndex,
        (Matrix.single r s (A r s) :
          Matrix SpaceIndex SpaceIndex ℝ) := Matrix.matrix_eq_sum_single A
    _ = ∑ r : SpaceIndex, ∑ s : SpaceIndex,
        (A r s) • (Matrix.single r s (1 : ℝ) :
          Matrix SpaceIndex SpaceIndex ℝ) := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hs
      simp only [Matrix.smul_single, smul_eq_mul, mul_one]

#print axioms coordinateSkewInput_entry
#print axioms coordinateMatrix9_coefficients_on_units

end
end FCP.BFSSPairedSpin9Plane
