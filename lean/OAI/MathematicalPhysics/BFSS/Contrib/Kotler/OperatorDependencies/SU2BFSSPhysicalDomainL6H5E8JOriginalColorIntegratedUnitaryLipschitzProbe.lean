import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8IOriginalColorIntegralConverseGeneratorDomainProbe
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
L6H5E8J — exact source original BFSS one-parameter color
unitary integrated-orbit operator is Lipschitz in the
Hilbert-space input with constant |t|.

The key analytic estimate for the CLOSED GRAPH TARGET:
  ‖ ∫_0^t U_c(s)w ds - ∫_0^t U_c(s)z ds ‖
     ≤ ‖w-z‖ * |t|.

This isolates a generic norm-nonincreasing CLM orbit and
pinned interval integral estimates, then instantiates the
previously qualified ORIGINAL FullL2 source unitary norm
theorem (G7W). No use of concrete Fock expressions during
abstract integral calculations.

Accepted inputs: H5E8I exact source integral converse,
H5A original strong orbit continuity, G7W all-vector norm
preservation, pinned Mathlib real-time integration calculus.
The graph-limit and closedness theorem are STILL OPEN.

No new assumptions, proxy source, altered +i sign, or
BFSS spectral claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8J
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6G7W
open FCP.BFSSSU2PhysicalDomainL6H5A
open MeasureTheory

/-- Banach-valued integrated orbit is Lipschitz in input
under norm-nonincreasing real continuous linear maps.
This estimates arbitrary signed interval 0..t. -/
theorem abstract_nonexpansive_orbit_integral_lipschitz
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (U : ℝ → E →L[ℝ] E)
    (hc : ∀ w : E, Continuous (fun s : ℝ => U s w))
    (hnorm : ∀ (s : ℝ) (w : E), ‖U s w‖ ≤ ‖w‖)
    (w z : E) (t : ℝ) :
    ‖(∫ s in (0 : ℝ)..t, U s w) -
        (∫ s in (0 : ℝ)..t, U s z)‖ ≤
      ‖w - z‖ * |t| := by
  have hw : IntervalIntegrable (fun s : ℝ => U s w)
      volume (0 : ℝ) t := (hc w).intervalIntegrable _ _
  have hz : IntervalIntegrable (fun s : ℝ => U s z)
      volume (0 : ℝ) t := (hc z).intervalIntegrable _ _
  have hfun :
      (fun s : ℝ => U s w - U s z) =
      (fun s : ℝ => U s (w - z)) := by
    funext s
    exact ((U s).map_sub w z).symm
  calc
    ‖(∫ s in (0 : ℝ)..t, U s w) -
        (∫ s in (0 : ℝ)..t, U s z)‖ =
        ‖∫ s in (0 : ℝ)..t, U s (w - z)‖ := by
      rw [← intervalIntegral.integral_sub hw hz]
      rw [hfun]
    _ ≤ ‖w - z‖ * |t| := by
      have hh :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (a := (0 : ℝ)) (b := t)
          (C := ‖w - z‖)
          (f := fun s : ℝ => U s (w - z))
          (fun s _ => hnorm s (w - z))
      simpa only [sub_zero] using hh

/-- For the GENUINE original BFSS source color action,
the Banach-valued time integral depends Lipschitz-
continuously on its FullL2 input; the constant is |t|.
No hidden generic substitute dynamics. -/
theorem actualOriginalColorOrbit_integral_lipschitz
    (c : ColorIndex 2) (w z : FullL2 2) (t : ℝ) :
    ‖(∫ s in (0 : ℝ)..t,
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c s) w) -
      (∫ s in (0 : ℝ)..t,
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c s) z)‖ ≤
      ‖w - z‖ * |t| := by
  let U : ℝ → FullL2 2 →L[ℝ] FullL2 2 :=
    fun s => (actualOriginalFullL2GaugePairCLM
      (sourcePlusIGaugeCurve c s)).restrictScalars ℝ
  have hcont : ∀ x : FullL2 2, Continuous (fun s : ℝ => U s x) := by
    intro x
    exact actualOriginalFullL2ColorCurve_orbit_continuous c x
  have hnorm : ∀ (s : ℝ) (x : FullL2 2),
      ‖U s x‖ ≤ ‖x‖ := by
    intro s x
    exact le_of_eq (actualOriginalFullL2GaugePair_norm
      (sourcePlusIGaugeCurve c s) x)
  exact abstract_nonexpansive_orbit_integral_lipschitz
    U hcont hnorm w z t

#print axioms abstract_nonexpansive_orbit_integral_lipschitz
#print axioms actualOriginalColorOrbit_integral_lipschitz
#check @actualOriginalColorOrbit_integral_lipschitz

end
end FCP.BFSSSU2PhysicalDomainL6H5E8J
