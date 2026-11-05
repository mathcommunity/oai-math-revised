import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8GOriginalColorGeneratorAllTimeOrbitDerivativeProbe
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
L6H5E8H — fundamental theorem of calculus for the true ORIGINAL
BFSS SU2 color gauge-unitary group on the exact maximal
infinitesimal-generator domain.

The source-exact full Hilbert orbit from qualified H5E8G
is continuously differentiable with strong real-time derivative
U_c(s) A_c v. The pinned Banach-valued fundamental theorem
therefore gives a source-exact integral / Duhamel identity:
 ∫ s in 0..t, U_c(s) A_c v = U_c(t) v - v.

This is a named prerequisite for a future graph-closedness proof
using norm limits and uniform isometric U_c(s); it is NOT a
closedness or skew-adjointness theorem by itself.

Source +i curve, inverse bosonic pullback, original Fock action
and full domain are unchanged. No new assumptions or axioms.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8H
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6H5A
open FCP.BFSSSU2PhysicalDomainL6H5E8E
open FCP.BFSSSU2PhysicalDomainL6H5E8G
open MeasureTheory

/-- An independent abstract Hilbert/Banach-valued FTC:
for a real-time differentiable orbit with a continuous
strong derivative, the derivative integrates to
the total vector-valued orbit difference. -/
theorem abstract_continuous_strong_derivative_integral
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) (hf : Differentiable ℝ f)
    (hc : Continuous (fun s : ℝ => deriv f s))
    (t : ℝ) :
    (∫ s in (0 : ℝ)..t, deriv f s) = f t - f 0 := by
  have hint :
      IntervalIntegrable (deriv f) volume (0 : ℝ) t :=
    hc.intervalIntegrable _ _
  exact intervalIntegral.integral_deriv_eq_sub
    (fun s _ => hf s) hint

/-- True ORIGINAL SU2 color unitary generator satisfies
the source-exact integrated evolution identity on its
full maximal real-time differentiability domain. -/
theorem actualOriginalColorGenerator_orbit_integral_eq_sub
    (c : ColorIndex 2)
    (v : actualOriginalColorGeneratorDomainSubmodule c)
    (t : ℝ) :
    (∫ s in (0 : ℝ)..t,
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c s)
        (actualOriginalColorGeneratorLinear c v)) =
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c t) (v : FullL2 2) -
        (v : FullL2 2) := by
  let orbit : ℝ → FullL2 2 :=
    fun s => actualOriginalFullL2GaugePairCLM
      (sourcePlusIGaugeCurve c s) (v : FullL2 2)
  have hdifferentiable : Differentiable ℝ orbit :=
    actualOriginalColorGenerator_orbit_differentiable c v
  have hcont : Continuous (fun s : ℝ => deriv orbit s) :=
    actualOriginalColorGenerator_orbit_deriv_continuous c v
  have hftc :
      (∫ s in (0 : ℝ)..t, deriv orbit s) =
      orbit t - orbit 0 :=
    abstract_continuous_strong_derivative_integral
      orbit hdifferentiable hcont t
  have hderiv :
      (fun s : ℝ => deriv orbit s) =
      (fun s : ℝ =>
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c s)
          (actualOriginalColorGeneratorLinear c v)) := by
    funext s
    exact actualOriginalColorGenerator_orbit_deriv_eq c v s
  rw [hderiv] at hftc
  change
    (∫ s in (0 : ℝ)..t,
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c s)
        (actualOriginalColorGeneratorLinear c v)) =
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c t) (v : FullL2 2) -
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c 0) (v : FullL2 2) at hftc
  rw [actualOriginalFullL2ColorCurve_zero] at hftc
  exact hftc

#print axioms abstract_continuous_strong_derivative_integral
#print axioms actualOriginalColorGenerator_orbit_integral_eq_sub
#check @actualOriginalColorGenerator_orbit_integral_eq_sub

end
end FCP.BFSSSU2PhysicalDomainL6H5E8H
