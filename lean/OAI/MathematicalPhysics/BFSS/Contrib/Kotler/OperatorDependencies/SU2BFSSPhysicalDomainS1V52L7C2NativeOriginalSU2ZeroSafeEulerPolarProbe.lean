import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L7B3NativeEulerWitnessSpinHomProbe
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
L7C2 — exact native original GaugeGroup 2 first-row norm and
zero-safe polar certificates as a THIN current-branch transport of
historical accepted L6H5E8V mathematics. We intentionally do not
import historical L6H5E8U/V because their upstream module closures
carry unrelated physical Gauss/Fock proofs absent from the qualified
current S1V52 cache.

No surrogate SU2, independent Pauli color, hidden regularity
hypothesis, nonzero-argument assumption or invented result.
The original first-row complex entries and the qualified
C1 originalNativeQuaternion_norm_one remain the only inputs.

Qualify all roots in strict source-pinned Lean CI before accepting.
This does not itself prove exact normalized source Euler times,
native curves, or unconditional source Spin group membership.
-/
set_option autoImplicit false
set_option maxHeartbeats 430000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSS1V52L7C2
noncomputable section
open OAI.BFSSQuantum
open FCP.BFSSS1V52B3
open FCP.BFSSS1V52C1

/-- Original native SU2 actual first-row complex squared norm. -/
theorem originalNativeFirstRow_norm_sq (g : GaugeGroup 2) :
    ‖((g : ColorMatrix 2) 0 0)‖ ^ 2 +
      ‖((g : ColorMatrix 2) 0 1)‖ ^ 2 = 1 := by
  have h := originalNativeQuaternion_norm_one g
  change ((g : ColorMatrix 2) 0 0).re ^ 2 +
      ((g : ColorMatrix 2) 0 0).im ^ 2 +
      ((g : ColorMatrix 2) 0 1).re ^ 2 +
      ((g : ColorMatrix 2) 0 1).im ^ 2 = 1 at h
  have hnorm : Complex.normSq ((g : ColorMatrix 2) 0 0) +
      Complex.normSq ((g : ColorMatrix 2) 0 1) = 1 := by
    rw [Complex.normSq_apply, Complex.normSq_apply]
    linarith [h]
  simpa only [Complex.normSq_eq_norm_sq] using hnorm

/-- First-row upper-right modulus never exceeds one,
for the ACTUAL original GaugeGroup 2. -/
theorem originalNativeFirstRow_v_norm_le_one (g : GaugeGroup 2) :
    ‖((g : ColorMatrix 2) 0 1)‖ ≤ 1 := by
  have h := originalNativeFirstRow_norm_sq g
  have hv : 0 ≤ ‖((g : ColorMatrix 2) 0 1)‖ := norm_nonneg _
  nlinarith [sq_nonneg ‖((g : ColorMatrix 2) 0 0)‖]

/-- The zero-safe middle Euler angle for the ACTUAL original native
SU2 group. Does not assume the (0,1) entry is nonzero. -/
def originalNativeMiddleAngle (g : GaugeGroup 2) : ℝ :=
  Real.arcsin ‖((g : ColorMatrix 2) 0 1)‖

theorem originalNativeMiddleAngle_sin (g : GaugeGroup 2) :
    Real.sin (originalNativeMiddleAngle g) =
      ‖((g : ColorMatrix 2) 0 1)‖ := by
  unfold originalNativeMiddleAngle
  exact Real.sin_arcsin (by have h := norm_nonneg ((g : ColorMatrix 2) 0 1); linarith)
    (originalNativeFirstRow_v_norm_le_one g)

theorem originalNativeMiddleAngle_cos (g : GaugeGroup 2) :
    Real.cos (originalNativeMiddleAngle g) =
      ‖((g : ColorMatrix 2) 0 0)‖ := by
  rw [originalNativeMiddleAngle, Real.cos_arcsin]
  have h := originalNativeFirstRow_norm_sq g
  have hsub : 1 - ‖((g : ColorMatrix 2) 0 1)‖ ^ 2 =
      ‖((g : ColorMatrix 2) 0 0)‖ ^ 2 := by linarith
  rw [hsub, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Pinned Mathlib zero-safe polar reconstruction, including u=0. -/
theorem originalNativeFirstRow_u_polar (g : GaugeGroup 2) :
    (‖((g : ColorMatrix 2) 0 0)‖ : ℂ) *
      Complex.exp (Complex.arg ((g : ColorMatrix 2) 0 0) * Complex.I) =
    (g : ColorMatrix 2) 0 0 :=
  Complex.norm_mul_exp_arg_mul_I ((g : ColorMatrix 2) 0 0)

/-- Pinned Mathlib zero-safe polar reconstruction, including v=0. -/
theorem originalNativeFirstRow_v_polar (g : GaugeGroup 2) :
    (‖((g : ColorMatrix 2) 0 1)‖ : ℂ) *
      Complex.exp (Complex.arg ((g : ColorMatrix 2) 0 1) * Complex.I) =
    (g : ColorMatrix 2) 0 1 :=
  Complex.norm_mul_exp_arg_mul_I ((g : ColorMatrix 2) 0 1)

#print axioms originalNativeFirstRow_norm_sq
#print axioms originalNativeFirstRow_v_norm_le_one
#print axioms originalNativeMiddleAngle
#print axioms originalNativeMiddleAngle_sin
#print axioms originalNativeMiddleAngle_cos
#print axioms originalNativeFirstRow_u_polar
#print axioms originalNativeFirstRow_v_polar
end
end FCP.BFSSS1V52L7C2
