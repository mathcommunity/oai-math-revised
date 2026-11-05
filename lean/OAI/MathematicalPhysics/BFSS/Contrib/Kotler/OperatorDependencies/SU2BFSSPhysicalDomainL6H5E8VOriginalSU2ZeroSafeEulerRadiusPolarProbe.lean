import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8UOriginalSourceZYZProductMatrixProbe
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
L6H5E8V: genuine SU(2) quaternion first-row norm and ZERO-SAFE
polar/trigonometric witness interface for original-source ZYZ.

Accepted source:
H5E8Q original gauge-matrix quaternion/norm-sphere (#342)
H5E8U original positive-i source ZYZ matrix and subgroup (#350).

No Euler factorization, gauge generation, nonzero-phase hypothesis,
or Fock representation asserted here. In particular, pinned
Complex.norm_mul_exp_arg_mul_I is valid also when the entry is 0.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8V
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2PhysicalDomainL6H5E8Q

def originalSU2RowU (g : GaugeGroup 2) : ℂ :=
  (g : ColorMatrix 2) 0 0

def originalSU2RowV (g : GaugeGroup 2) : ℂ :=
  (g : ColorMatrix 2) 0 1

/-- Exact real squared-modulus form of the already-qualified
original source quaternion unit-sphere norm equation. -/
theorem originalSU2_row_norm_sq (g : GaugeGroup 2) :
    ‖originalSU2RowU g‖ ^ 2 + ‖originalSU2RowV g‖ ^ 2 = 1 := by
  have h := originalSU2_firstRow_normSq_eq_one g
  change Complex.normSq (originalSU2RowU g) +
    Complex.normSq (originalSU2RowV g) = 1 at h
  simpa only [Complex.normSq_eq_norm_sq] using h

theorem originalSU2_row_v_norm_le_one (g : GaugeGroup 2) :
    ‖originalSU2RowV g‖ ≤ 1 := by
  have h := originalSU2_row_norm_sq g
  have hu : 0 ≤ ‖originalSU2RowU g‖ := norm_nonneg _
  have hv : 0 ≤ ‖originalSU2RowV g‖ := norm_nonneg _
  nlinarith [sq_nonneg ‖originalSU2RowU g‖]

/-- The Euler middle angle. No zero-entry or endpoint exception. -/
def originalSU2MiddleAngle (g : GaugeGroup 2) : ℝ :=
  Real.arcsin ‖originalSU2RowV g‖

theorem originalSU2_middle_sin (g : GaugeGroup 2) :
    Real.sin (originalSU2MiddleAngle g) = ‖originalSU2RowV g‖ := by
  unfold originalSU2MiddleAngle
  exact Real.sin_arcsin (by have h := norm_nonneg (originalSU2RowV g); linarith)
    (originalSU2_row_v_norm_le_one g)

theorem originalSU2_middle_cos (g : GaugeGroup 2) :
    Real.cos (originalSU2MiddleAngle g) = ‖originalSU2RowU g‖ := by
  rw [originalSU2MiddleAngle, Real.cos_arcsin]
  have h := originalSU2_row_norm_sq g
  have hsub : 1 - ‖originalSU2RowV g‖ ^ 2 =
      ‖originalSU2RowU g‖ ^ 2 := by linarith
  rw [hsub, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Pinned Mathlib polar reconstruction is VALID EVEN WHEN u = 0. -/
theorem originalSU2_row_u_zero_safe_polar (g : GaugeGroup 2) :
    (‖originalSU2RowU g‖ : ℂ) *
        Complex.exp (Complex.arg (originalSU2RowU g) * Complex.I) =
      originalSU2RowU g :=
  Complex.norm_mul_exp_arg_mul_I (originalSU2RowU g)

/-- Pinned Mathlib polar reconstruction is VALID EVEN WHEN v = 0. -/
theorem originalSU2_row_v_zero_safe_polar (g : GaugeGroup 2) :
    (‖originalSU2RowV g‖ : ℂ) *
        Complex.exp (Complex.arg (originalSU2RowV g) * Complex.I) =
      originalSU2RowV g :=
  Complex.norm_mul_exp_arg_mul_I (originalSU2RowV g)

#print axioms originalSU2RowU
#print axioms originalSU2RowV
#print axioms originalSU2_row_norm_sq
#print axioms originalSU2_row_v_norm_le_one
#print axioms originalSU2MiddleAngle
#print axioms originalSU2_middle_sin
#print axioms originalSU2_middle_cos
#print axioms originalSU2_row_u_zero_safe_polar
#print axioms originalSU2_row_v_zero_safe_polar
#check @originalSU2_middle_cos

end
end FCP.BFSSSU2PhysicalDomainL6H5E8V
