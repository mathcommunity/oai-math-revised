import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K6PhysicalTrialEnergyLowerProbe

/-!
# BFSS SU(2) G4-K7 — correct the trial-energy lower-bound interpretation

Gate #136 compiled a uniform lower estimate -K for the actual
nonzero SU(2) physical trial state. A closer pinned-source audit
found that this bound is non-sharp for a SIMPLE MATHEMATICAL REASON:
the *literal source definition* of deformedCoreEnergy in
BFSS/MassiveMoments.lean is a positive 1/16 times a finite sum of
squared L² norms of the deformed supercharges.

Thus the strongest immediate universal sign conclusion is
ZERO ≤ deformedCoreEnergy for EVERY source-defined SmoothCore
state and EVERY real h,m, not just for our one test state.

This candidate does not take credit for a new energy estimate:
it makes the stronger source consequence explicit and develops
the exact zero-mode / strict-positivity criterion for our true
nonzero physical SU(2) test state. The next OPEN task is to
discharge a specific nonzero deformed-charge witness, rather
than mistake nonnegative energy for positive energy, a spectral
gap, a Hamiltonian eigenstate, or a supersymmetric ground state.
-/

namespace FCP.BFSSSU2GaugeG4K7
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4K2B
open FCP.BFSSSU2GaugeG4K3
open FCP.BFSSSU2GaugeG4K6

/-- Exact source-defined nonnegativity, for ALL smooth-core
states in actual pinned AlgebraData 2 and all real h,m.
This is a transparent finite sum-of-squares, not a new
spectral estimate. -/
theorem pairedDeformedCoreEnergy_nonneg
    (h m : ℝ) (f : SmoothCore 2) :
    0 ≤ pairedAlgebraData.deformedCoreEnergy h m f := by
  change 0 ≤ (1 / 16 : ℝ) *
    ∑ α : SpinIndex,
      ‖coreToL2 (pairedAlgebraData.deformedCoreCharge h m α f)‖ ^ 2
  exact mul_nonneg (by norm_num)
    (Finset.sum_nonneg (fun α _ => sq_nonneg _))

/-- The same nonnegativity for the particular previously
certified nonzero, smooth, gauge-physical trial state. -/
theorem physicalDeformedEnergy_nonneg (h m : ℝ) :
    0 ≤ physicalDeformedEnergy h m :=
  pairedDeformedCoreEnergy_nonneg h m radialBumpSmoothCore

/-- For the source sum of squares, the energy vanishes if and
only if EVERY component of the genuine deformed charge vector
vanishes in the actual FullL2 2 Hilbert space.
No such simultaneous vanishing is claimed here. -/
theorem pairedDeformedCoreEnergy_zero_iff (h m : ℝ)
    (f : SmoothCore 2) :
    pairedAlgebraData.deformedCoreEnergy h m f = 0 ↔
      ∀ α : SpinIndex,
        coreToL2 (pairedAlgebraData.deformedCoreCharge h m α f) = 0 := by
  change (1 / 16 : ℝ) *
    (∑ α : SpinIndex,
      ‖coreToL2 (pairedAlgebraData.deformedCoreCharge h m α f)‖ ^ 2) = 0 ↔ _
  rw [mul_eq_zero]
  have hc : (1 / 16 : ℝ) ≠ 0 := by norm_num
  simp only [hc, false_or]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun α _ => sq_nonneg _)]
  simp only [Finset.mem_univ, true_implies, sq_eq_zero_iff, norm_eq_zero]

/-- The exact zero-energy condition on OUR nonzero physical
trial state; nonzero Hilbert norm of the state itself cannot
replace the obligation to inspect its deformed supercharges. -/
theorem physicalDeformedEnergy_zero_iff (h m : ℝ) :
    physicalDeformedEnergy h m = 0 ↔
      ∀ α : SpinIndex,
        coreToL2 (pairedAlgebraData.deformedCoreCharge h m α
          radialBumpSmoothCore) = 0 :=
  pairedDeformedCoreEnergy_zero_iff h m radialBumpSmoothCore

/-- Strict positivity is logically EQUIVALENT to at least
one actual deformed supercharge vector component being nonzero.
This theorem does NOT assert such a component exists. -/
theorem physicalDeformedEnergy_pos_iff (h m : ℝ) :
    0 < physicalDeformedEnergy h m ↔
      ∃ α : SpinIndex,
        coreToL2 (pairedAlgebraData.deformedCoreCharge h m α
          radialBumpSmoothCore) ≠ 0 := by
  constructor
  · intro hpos
    by_contra hn
    push_neg at hn
    have hzero : physicalDeformedEnergy h m = 0 :=
      (physicalDeformedEnergy_zero_iff h m).mpr hn
    exact (ne_of_gt hpos) hzero
  · rintro ⟨α, hα⟩
    have hne : physicalDeformedEnergy h m ≠ 0 := by
      intro hz
      exact hα ((physicalDeformedEnergy_zero_iff h m).mp hz α)
    exact lt_of_le_of_ne (physicalDeformedEnergy_nonneg h m) hne.symm

/-- Corrected universal lower bound for the normalized
physical trial energy: K=0 works for ALL real h, not
merely the restricted 0<h≤1 interval and m=1.
It follows from the exact squared-charge definition. -/
theorem physicalNormalizedTrialEnergy_nonneg (h : ℝ) :
    0 ≤ physicalNormalizedTrialEnergy h := by
  change 0 ≤ physicalDeformedEnergy h 1 / ‖radialBumpL2‖ ^ 2
  exact div_nonneg (physicalDeformedEnergy_nonneg h 1)
    (sq_nonneg _)

/-- Stronger explicit witness than the K6 existential negative
constant bound. K=0, including h outside (0,1], is valid. -/
theorem uniform_trialEnergy_lower_with_K_zero :
    ∀ h : ℝ, 0 ≤ physicalNormalizedTrialEnergy h :=
  physicalNormalizedTrialEnergy_nonneg

#print axioms pairedDeformedCoreEnergy_nonneg
#print axioms physicalDeformedEnergy_nonneg
#print axioms pairedDeformedCoreEnergy_zero_iff
#print axioms physicalDeformedEnergy_zero_iff
#print axioms physicalDeformedEnergy_pos_iff
#print axioms physicalNormalizedTrialEnergy_nonneg
#print axioms uniform_trialEnergy_lower_with_K_zero

end
end FCP.BFSSSU2GaugeG4K7
