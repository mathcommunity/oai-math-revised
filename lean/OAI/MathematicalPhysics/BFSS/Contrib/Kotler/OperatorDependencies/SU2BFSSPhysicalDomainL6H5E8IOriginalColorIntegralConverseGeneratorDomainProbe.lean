import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8HOriginalColorGeneratorOrbitFundamentalTheoremProbe
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
L6H5E8I — exact source integral-identity converse for the
ORIGINAL BFSS color infinitesimal generator.

If a vector pair (v, w) satisfies the original unitary
evolution integral equation for ALL times,
    ∫_0^t U_c(s) w ds = U_c(t) v - v,
then the orbit of v is strongly differentiable at t=0 with
derivative w. Thus v belongs to exactly the original maximal
generator domain and its genuine Gauss infinitesimal generator
equals w.

This is a necessary component of a closed-graph proof:
H5E8H produces the integral identity for members of the graph;
this theorem recovers graph membership from that identity.
The separate step of passing to norm limits under a bounded
unitary integral remains OPEN.

Use only qualified original source gauge maps, pinned Banach
FTC-1 and original +i, inverse-boson, Fock conventions.
No substitute operator, new axioms, closed-graph or spectral claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8I
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6H5A
open FCP.BFSSSU2PhysicalDomainL6H5E8E
open MeasureTheory

/-- Abstract converse to the real-time Banach-valued FTC.
The defining integrated orbit identity forces the strong
orbit derivative at t=0, without assuming differentiability
of the first orbit at the outset. -/
theorem abstract_orbit_integral_identity_hasDerivAt
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (U : ℝ → E →L[ℝ] E) (v w : E)
    (hzero : U 0 w = w)
    (hwcont : Continuous (fun s : ℝ => U s w))
    (hidentity : ∀ t : ℝ,
      (∫ s in (0 : ℝ)..t, U s w) = U t v - v) :
    HasDerivAt (fun t : ℝ => U t v) w 0 := by
  have hint :
      IntervalIntegrable (fun s : ℝ => U s w)
        volume (0 : ℝ) (0 : ℝ) :=
    hwcont.intervalIntegrable _ _
  have hFTC :
      HasDerivAt
        (fun t : ℝ => ∫ s in (0 : ℝ)..t, U s w)
        (U 0 w) 0 :=
    intervalIntegral.integral_hasDerivAt_right hint
      hwcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hwcont.continuousAt
  have hfun :
      (fun t : ℝ => ∫ s in (0 : ℝ)..t, U s w) =
      (fun t : ℝ => U t v - v) := by
    funext t
    exact hidentity t
  rw [hfun] at hFTC
  have hplus := hFTC.add_const v
  have hcancel :
      (fun t : ℝ => (U t v - v) + v) =
      (fun t : ℝ => U t v) := by
    funext t
    exact sub_add_cancel _ _
  change HasDerivAt
    (fun t : ℝ => (U t v - v) + v) (U 0 w) 0 at hplus
  rw [hcancel, hzero] at hplus
  exact hplus

/-- Original BFSS color integrated orbit identity implies
membership in the TRUE maximal source generator domain.
This is not an assumption of gauge invariance. -/
theorem actualOriginalColorIntegral_implies_generatorDomain
    (c : ColorIndex 2) (v w : FullL2 2)
    (hidentity : ∀ t : ℝ,
      (∫ s in (0 : ℝ)..t,
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c s) w) =
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c t) v - v) :
    v ∈ actualOriginalColorGeneratorDomainSubmodule c := by
  let U : ℝ → FullL2 2 →L[ℝ] FullL2 2 :=
    fun t => (actualOriginalFullL2GaugePairCLM
      (sourcePlusIGaugeCurve c t)).restrictScalars ℝ
  have hz : U 0 w = w := by
    exact actualOriginalFullL2ColorCurve_zero c w
  have hc : Continuous (fun t : ℝ => U t w) := by
    exact actualOriginalFullL2ColorCurve_orbit_continuous c w
  have he : ∀ t : ℝ,
      (∫ s in (0 : ℝ)..t, U s w) = U t v - v := hidentity
  have hd := abstract_orbit_integral_identity_hasDerivAt
    U v w hz hc he
  exact hd.differentiableAt

/-- On the source integral-identity criterion, the unique
strong derivative is the named original Gauss generator. -/
theorem actualOriginalColorIntegral_implies_generator_eq
    (c : ColorIndex 2) (v w : FullL2 2)
    (hidentity : ∀ t : ℝ,
      (∫ s in (0 : ℝ)..t,
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c s) w) =
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c t) v - v) :
    actualOriginalColorGeneratorLinear c
      ⟨v, actualOriginalColorIntegral_implies_generatorDomain
        c v w hidentity⟩ = w := by
  let U : ℝ → FullL2 2 →L[ℝ] FullL2 2 :=
    fun t => (actualOriginalFullL2GaugePairCLM
      (sourcePlusIGaugeCurve c t)).restrictScalars ℝ
  have hz : U 0 w = w := by
    exact actualOriginalFullL2ColorCurve_zero c w
  have hc : Continuous (fun t : ℝ => U t w) := by
    exact actualOriginalFullL2ColorCurve_orbit_continuous c w
  have he : ∀ t : ℝ,
      (∫ s in (0 : ℝ)..t, U s w) = U t v - v := hidentity
  have hd := abstract_orbit_integral_identity_hasDerivAt
    U v w hz hc he
  change deriv
    (fun t : ℝ =>
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c t) v) 0 = w
  exact hd.deriv

#print axioms abstract_orbit_integral_identity_hasDerivAt
#print axioms actualOriginalColorIntegral_implies_generatorDomain
#print axioms actualOriginalColorIntegral_implies_generator_eq
#check @actualOriginalColorIntegral_implies_generator_eq

end
end FCP.BFSSSU2PhysicalDomainL6H5E8I
