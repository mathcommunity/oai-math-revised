import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10FSourceGammaSymmetricPositiveQuadraticProbe
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Spectrum

/-!
K1D18V10H-F10G — original gamma16 real spectral API bridge.

After F9 accepted squared determinant magnitude, F10E accepted
tracelessness of all ORIGINAL source nine-vector gamma matrices,
and F10F accepted symmetry and strict positivity of original Q,
the next obligation is to enter the exact PINNED Mathlib real
Hermitian spectral theorem, not to guess eigenvalue multiplicities.

This tests three exact types:
1. Gamma(v) is Hermitian (over the original REAL 16-index carrier);
2. its real eigenvalues sum to zero;
3. their product is the original det Gamma(v).

The existing accepted source gamma is unchanged. The extra
eigenvalue property lambda^2=Q(v), the eight/eight multiplicity,
and positive determinant are NOT proved by this module.
No private original gamma table, substitute representation,
changes to Fock-order basis, unproved connectedness, or axioms.

F10G remains UNQUALIFIED until pinned fresh warningAsError
and independent exact type/axiom audit.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9DetFixture
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9Clifford
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- The exact original gamma real linear map is Hermitian
from the accepted F10F public source symmetry. -/
theorem gammaNineRealLinear_isHermitian
    (v : SpaceIndex → ℝ) :
    (gammaNineRealLinear v).IsHermitian := by
  exact Matrix.isHermitian_iff_isSymm.mpr
    (gammaNineRealLinear_isSymm v)

/-- The eigenvalues indexed by the exact original Fin16
spinor carrier sum to ZERO, from F10E's source-exact trace
and pinned Mathlib spectral trace formula. -/
theorem gammaNineRealLinear_realEigenvalues_sum_zero
    (v : SpaceIndex → ℝ) :
    (∑ i : SpinIndex,
      ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ)) = 0 := by
  calc
    (∑ i : SpinIndex,
        ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ)) =
        Matrix.trace (gammaNineRealLinear v) :=
      (Matrix.IsHermitian.trace_eq_sum_eigenvalues
        (gammaNineRealLinear_isHermitian v)).symm
    _ = 0 := gammaNineRealLinear_trace_zero v

/-- The original 16x16 determinant is the product of
real spectral eigenvalues. This does NOT select the
positive branch of the F9 determinant formula. -/
theorem gammaNineRealLinear_det_eq_realEigenvalues_prod
    (v : SpaceIndex → ℝ) :
    (gammaNineRealLinear v).det =
      ∏ i : SpinIndex,
        ((gammaNineRealLinear_isHermitian v).eigenvalues i : ℝ) := by
  exact Matrix.IsHermitian.det_eq_prod_eigenvalues
    (gammaNineRealLinear_isHermitian v)

#print axioms gammaNineRealLinear_isHermitian
#print axioms gammaNineRealLinear_realEigenvalues_sum_zero
#print axioms gammaNineRealLinear_det_eq_realEigenvalues_prod

end
end FCP.BFSSPairedSpin9DetFixture
