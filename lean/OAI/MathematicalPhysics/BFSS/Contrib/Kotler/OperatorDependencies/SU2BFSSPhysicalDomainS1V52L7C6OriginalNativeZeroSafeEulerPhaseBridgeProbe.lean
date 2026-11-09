import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L7C5OriginalNativeZYZCircleFactorsProbe

/-!
S1V52-L7C6 — STAGED, NOT KERNEL-QUALIFIED.
Preserve the genuine original positive-i native SU2 first-row
complex phases, and solve the *exact* original quaternion ZYZ
phase system: left+right = arg u, left-right = arg v.

This is the zero-safe source route, including u=0 and v=0:
the accepted L7C2 polar identities are unconditional, so
no division by a complex entry or hidden nonzero hypothesis.
The real original middle angle is the L7C2 arcsine of ‖v‖;
no t/2 or pauliScale substitution is made.

Actual native Z/Y factor group construction from L7C5
and original full native matrix reconstruction C2C will be
used later. This phase source itself is unqualified and does
not claim equality of arbitrary g with a ZYZ product.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000

namespace FCP.BFSSS1V52L7C6
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V52L7C2
open FCP.BFSSS1V52L7C5

/-- Genuine original SU2 source upper-left / upper-right phases
without nonzero-argument assumptions. -/
noncomputable def originalNativeEulerLeftAngle (g : GaugeGroup 2) : ℝ :=
  (Complex.arg ((g : ColorMatrix 2) 0 0) +
    Complex.arg ((g : ColorMatrix 2) 0 1)) / 2

noncomputable def originalNativeEulerRightAngle (g : GaugeGroup 2) : ℝ :=
  (Complex.arg ((g : ColorMatrix 2) 0 0) -
    Complex.arg ((g : ColorMatrix 2) 0 1)) / 2

/-- Original positive-i ZYZ upper-left sum phase. -/
theorem originalNativeEulerPhase_sum (g : GaugeGroup 2) :
    originalNativeEulerLeftAngle g + originalNativeEulerRightAngle g =
      Complex.arg ((g : ColorMatrix 2) 0 0) := by
  dsimp [originalNativeEulerLeftAngle, originalNativeEulerRightAngle]
  ring

/-- Original positive-i ZYZ upper-right difference phase. -/
theorem originalNativeEulerPhase_diff (g : GaugeGroup 2) :
    originalNativeEulerLeftAngle g - originalNativeEulerRightAngle g =
      Complex.arg ((g : ColorMatrix 2) 0 1) := by
  dsimp [originalNativeEulerLeftAngle, originalNativeEulerRightAngle]
  ring

/-- EXACT native first-row u component reconstructed at angles
computed from that very native original SU2 matrix.
Remains correct when the original upper-left entry vanishes. -/
theorem originalNativeEulerPhase_reconstruct_u (g : GaugeGroup 2) :
    ((Real.cos (originalNativeMiddleAngle g) : ℝ) : ℂ) *
      ((Real.cos (originalNativeEulerLeftAngle g +
           originalNativeEulerRightAngle g) : ℂ) +
        (Real.sin (originalNativeEulerLeftAngle g +
           originalNativeEulerRightAngle g) : ℂ) * Complex.I) =
        (g : ColorMatrix 2) 0 0 := by
  rw [originalNativeEulerPhase_sum, originalNativeMiddleAngle_cos]
  simpa only [Complex.exp_ofReal_mul_I] using
    (originalNativeFirstRow_u_polar g)

/-- EXACT native first-row v component, including v=0.
The phase is left-right, not left+right. -/
theorem originalNativeEulerPhase_reconstruct_v (g : GaugeGroup 2) :
    ((Real.sin (originalNativeMiddleAngle g) : ℝ) : ℂ) *
      ((Real.cos (originalNativeEulerLeftAngle g -
           originalNativeEulerRightAngle g) : ℂ) +
        (Real.sin (originalNativeEulerLeftAngle g -
           originalNativeEulerRightAngle g) : ℂ) * Complex.I) =
        (g : ColorMatrix 2) 0 1 := by
  rw [originalNativeEulerPhase_diff, originalNativeMiddleAngle_sin]
  simpa only [Complex.exp_ofReal_mul_I] using
    (originalNativeFirstRow_v_polar g)

#print axioms originalNativeEulerLeftAngle
#print axioms originalNativeEulerRightAngle
#print axioms originalNativeEulerPhase_sum
#print axioms originalNativeEulerPhase_diff
#print axioms originalNativeEulerPhase_reconstruct_u
#print axioms originalNativeEulerPhase_reconstruct_v
end
end FCP.BFSSS1V52L7C6
