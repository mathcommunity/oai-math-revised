import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10HSourceGammaEigenvalueSquareProbe
import Mathlib.Analysis.Real.Sqrt

/-!
V10H-F10I — exact original gamma16 real eigenvalue TWO-SIGN square-root gate.

F10H is strict-verified. Its original (not substitute) real Hermitian
eigenvalues satisfy lambda_i(v) * lambda_i(v) = Q(v).
F10F proves Q is the exact Euclidean finite sum of squares and
positive for v nonzero. Pinned Mathlib includes Real.mul_self_sqrt
and the already-qualified F9 proof uses mul_self_eq_mul_self_iff.

This module tests two small statements:
* every original gamma eigenvalue lies in {+sqrt Q,-sqrt Q};
* sqrt Q is positive whenever the original source vector is nonzero.

No assumption on eigenvalue counts or determinant sign. No private
original gamma tables, invented matrix, changes to Fock pairing,
resource-limit changes or extra axioms.
F10I CANDIDATE until all strict independent audits pass.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9DetFixture
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9Clifford
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- The original source quadratic form is nonnegative
for EVERY original nine-vector, including zero. -/
theorem source9Quadratic_nonneg
    (v : SpaceIndex → ℝ) : 0 ≤ source9Quadratic v := by
  by_cases hv : v = 0
  · subst v
    rw [source9Quadratic_eq_dot]
    simp
  · exact le_of_lt (source9Quadratic_pos_of_ne v hv)

/-- Each exact ORIGINAL source real gamma16 eigenvalue is
one of the two square roots of the ORIGINAL quadratic form. -/
theorem gammaNineRealLinear_realEigenvalues_eq_sqrt_or_neg
    (v : SpaceIndex → ℝ) (i : SpinIndex) :
    (gammaNineRealLinear_isHermitian v).eigenvalues i =
        Real.sqrt (source9Quadratic v) ∨
    (gammaNineRealLinear_isHermitian v).eigenvalues i =
        -(Real.sqrt (source9Quadratic v)) := by
  have hQ : 0 ≤ source9Quadratic v :=
    source9Quadratic_nonneg v
  have hsqrt :
      Real.sqrt (source9Quadratic v) *
        Real.sqrt (source9Quadratic v) = source9Quadratic v :=
    Real.mul_self_sqrt hQ
  have hsq := gammaNineRealLinear_realEigenvalues_mul_self v i
  exact (mul_self_eq_mul_self_iff).mp (hsq.trans hsqrt.symm)

/-- For a nonzero ORIGINAL source nine-vector, the
positive square-root value is strictly positive. -/
theorem source9Quadratic_sqrt_pos_of_ne
    (v : SpaceIndex → ℝ) (hv : v ≠ 0) :
    0 < Real.sqrt (source9Quadratic v) := by
  exact Real.sqrt_pos.2 (source9Quadratic_pos_of_ne v hv)

#print axioms source9Quadratic_nonneg
#print axioms gammaNineRealLinear_realEigenvalues_eq_sqrt_or_neg
#print axioms source9Quadratic_sqrt_pos_of_ne

end
end FCP.BFSSPairedSpin9DetFixture
