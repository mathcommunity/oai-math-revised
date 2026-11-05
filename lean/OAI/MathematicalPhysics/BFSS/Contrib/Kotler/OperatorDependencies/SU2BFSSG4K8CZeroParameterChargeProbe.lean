import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K8BNonzeroCoordinateL2Probe

/-!
# BFSS SU(2) G4-K8C — all exact first-order charge components nonzero;
# zero-parameter source charge and trial-energy positivity

Gate #143 proves that the PINNED coordinate derivatives of our
nonzero smooth SU(2) Gauss-invariant radial state have strictly
positive total kinetic L² energy.

The upstream source KineticSkewCore_norm identifies EVERY
spin-indexed exact first-order supercharge L² norm squared with
one half of the SAME kinetic sum. We prove each component is
nonzero, not merely that some coordinate derivative is nonzero.

For the special zero deformation h=m=0, the PINNED upstream
deformedRealField_polarized theorem proves that the potential
multiplication field is exactly zero. Thus the source
deformedCoreCharge at h=m=0 is the actual source kinetic
firstOrder charge, with a nonzero L² image for every spin
component. The source-derived sum-of-squares criterion then
gives strictly positive DEFORMED TRIAL ENERGY at h=m=0.

IMPORTANT SCIENTIFIC BOUNDARY:
This h=m=0 theory is the free/kinetic zero-parameter limit.
It is NOT the interacting BFSS case (h=1, m=0), nor the
positive-mass deformation h>0,m>0, nor a spectral lower bound.
Strict positivity for this single Gauss-invariant trial state
does NOT give a spectral gap or a ground-state claim. The
next substantive task is to transport a nonzero charge to
genuine nonzero interaction/deformation parameters without
assuming the absence of kinetic/potential cancellation.
-/

namespace FCP.BFSSSU2GaugeG4K8C
noncomputable section

open scoped BigOperators
open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open MeasureTheory
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2GaugeG4K2B
open FCP.BFSSSU2GaugeG4K3
open FCP.BFSSSU2GaugeG4K5
open FCP.BFSSSU2GaugeG4K6
open FCP.BFSSSU2GaugeG4K7
open FCP.BFSSSU2GaugeG4K8B

/-- EVERY one of 16 actual pinned first-order BFSS charge
images is strictly nonzero in L² for our nonzero
smooth SU(2) Gauss-invariant state. This uses the
upstream kineticSkewCore_norm identity, not a
surrogate kinetic operator. -/
theorem physicalKineticFirstOrder_norm_sq_pos (α : SpinIndex) :
    0 < ‖coreToL2
        (MixedEnergy.firstOrder (pairedAlgebraData.kineticSkewSymbol α)
          radialBumpSmoothCore)‖ ^ 2 := by
  rw [pairedAlgebraData.kineticSkewCore_norm,
      ← physicalKineticDensity_integral_exact]
  exact mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
    physicalKineticDensity_integral_pos

theorem physicalKineticFirstOrder_L2_ne_zero (α : SpinIndex) :
    coreToL2
      (MixedEnergy.firstOrder (pairedAlgebraData.kineticSkewSymbol α)
        radialBumpSmoothCore) ≠ 0 := by
  intro hz
  have hn := physicalKineticFirstOrder_norm_sq_pos α
  rw [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hn
  exact (not_lt_of_ge (le_refl (0 : ℝ))) hn

/-- Source-derived exact vanishing of the true BFSS
potential operator FIELD at zero interaction and mass. -/
theorem pairedDeformedRealField_zero_zero
    (α : SpinIndex) (x : Boson 2) :
    pairedAlgebraData.deformedRealField 0 0 α x = 0 := by
  rw [pairedAlgebraData.deformedRealField_polarized]
  apply ContinuousLinearMap.ext
  intro z
  simp [IsSMulApply.smul_apply, ContinuousLinearMap.smul_apply]

/-- At h=m=0, the actual deformedCoreCharge equals the
source first-order kinetic charge AS A SMOOTH CORE SECTION.
This result does not identify positive coupling h>0
with the free limit. -/
theorem physicalZeroParametersCharge_eq_firstOrder (α : SpinIndex) :
    pairedAlgebraData.deformedCoreCharge 0 0 α radialBumpSmoothCore =
      MixedEnergy.firstOrder
        (pairedAlgebraData.kineticSkewSymbol α) radialBumpSmoothCore := by
  have hzeroField :
      MixedEnergy.field
        (pairedAlgebraData.deformedRealField 0 0 α)
        (pairedAlgebraData.deformedRealField_contDiff 0 0 α)
        radialBumpSmoothCore = 0 := by
    apply DFunLike.ext
    intro x
    rw [MixedEnergy.field_apply, pairedDeformedRealField_zero_zero]
    simp
  calc
    pairedAlgebraData.deformedCoreCharge 0 0 α radialBumpSmoothCore =
        MixedEnergy.firstOrder
          (pairedAlgebraData.kineticSkewSymbol α) radialBumpSmoothCore +
        MixedEnergy.field
          (pairedAlgebraData.deformedRealField 0 0 α)
          (pairedAlgebraData.deformedRealField_contDiff 0 0 α)
          radialBumpSmoothCore := rfl
    _ = _ := by rw [hzeroField, add_zero]

/-- Nonzero L² DEFORMED charge component in the literal
zero-coupling, zero-mass source specialization; ALL 16
components are nonzero. -/
theorem physicalZeroParametersCharge_L2_ne_zero (α : SpinIndex) :
    coreToL2
      (pairedAlgebraData.deformedCoreCharge 0 0 α radialBumpSmoothCore) ≠ 0 := by
  rw [physicalZeroParametersCharge_eq_firstOrder]
  exact physicalKineticFirstOrder_L2_ne_zero α

/-- Positive total deformed quadratic trial energy at the
FREE zero-parameter point. Uses the Gate #138 exactly
proved strict-positivity iff, discharged by an explicit
spin index witness, rather than assuming positive energy. -/
theorem physicalDeformedEnergy_zeroParameters_pos :
    0 < physicalDeformedEnergy 0 0 := by
  apply (physicalDeformedEnergy_pos_iff 0 0).mpr
  exact ⟨(0 : SpinIndex), physicalZeroParametersCharge_L2_ne_zero 0⟩

/-- Strictly positive normalized physical trial quotient at
the free limit, with the previous positively certified
norm-squared denominator. This is not an infimum of the
energy spectrum or a positive spectral gap. -/
theorem physicalNormalizedTrialEnergy_zeroParameters_pos :
    0 < physicalDeformedEnergy 0 0 / ‖radialBumpL2‖ ^ 2 :=
  div_pos physicalDeformedEnergy_zeroParameters_pos
    radialBumpL2_norm_sq_pos

#print axioms physicalKineticFirstOrder_norm_sq_pos
#print axioms physicalKineticFirstOrder_L2_ne_zero
#print axioms pairedDeformedRealField_zero_zero
#print axioms physicalZeroParametersCharge_eq_firstOrder
#print axioms physicalZeroParametersCharge_L2_ne_zero
#print axioms physicalDeformedEnergy_zeroParameters_pos
#print axioms physicalNormalizedTrialEnergy_zeroParameters_pos

end
end FCP.BFSSSU2GaugeG4K8C
