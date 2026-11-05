import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5D1OriginalSmoothGaugeOrbitPointwiseGroupLawProbe
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

/-!
L6H5D2: propagate the EXACT original SU2 +i color gauge-orbit
Gauss-candidate derivative from t=0 to a translated curve at t.

The original H5D1 source group law and the qualified H5C3
source Gauss derivative are combined through the REAL-linear
restriction of the original COMPLEX-linear fermion gauge isometry.
No expansion of the 48 Majorana operators and no substitute gauge
action. Strong FullL2 differentiation and closed-generator claims
are beyond this leaf.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5D2
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6H0
open FCP.BFSSSU2PhysicalDomainL6H5B
open FCP.BFSSSU2PhysicalDomainL6H5C3
open FCP.BFSSSU2PhysicalDomainL6H5D1

/-- The actual full original Fock/boson orbit differentiates as a
time-translated pointwise curve. Its derivative is the genuine
transported original Gauss candidate, not an assumed generator. -/
theorem actualOriginalSmoothGaugeOrbit_colorCurve_shifted_hasDerivAt_zero
    (c : ColorIndex 2) (f : SmoothCore 2)
    (t : ℝ) (x : Boson 2) :
    HasDerivAt
      (fun s : ℝ =>
        actualOriginalSmoothGaugeOrbitRepresentative f
          (sourcePlusIGaugeCurve c (t + s)) x)
      (pairedGaugeData.fermion (sourcePlusIGaugeCurve c t)
        ((actualOriginalCoreColorGaussCandidate c f)
          (pairedGaugeData.boson (sourcePlusIGaugeCurve c t)⁻¹ x)))
      0 := by
  let y : Boson 2 :=
    pairedGaugeData.boson (sourcePlusIGaugeCurve c t)⁻¹ x
  have hzero :=
    actualOriginalSmoothGaugeOrbit_gaussCandidate_pointwise_derivative_zero
      c f y
  -- #277: keep the source isometry-to-CLM projection as a single
  -- chained field expression. A line-leading .toContinuousLinearMap
  -- was parsed as a projection on the fiber element instead.
  let F : Fermion 2 →L[ℝ] Fermion 2 :=
    ((pairedGaugeData.fermion (sourcePlusIGaugeCurve c t)).toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
  have htrans := F.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hzero
  change HasDerivAt
    (fun s : ℝ =>
      pairedGaugeData.fermion (sourcePlusIGaugeCurve c t)
        (actualOriginalSmoothGaugeOrbitRepresentative f
          (sourcePlusIGaugeCurve c s) y))
    (pairedGaugeData.fermion (sourcePlusIGaugeCurve c t)
      ((actualOriginalCoreColorGaussCandidate c f) y))
    0 at htrans
  -- Gate #278: applying the source group law against the local `y`
  -- definition forced Lean into large concrete Fock definitional
  -- equality checks at both final `exact` applications.
  -- Formulate the curve identity *literally* as qualified by H5D1,
  -- without an abbreviation in the dependent theorem statement.
  have hcurve :
      (fun s : ℝ =>
        actualOriginalSmoothGaugeOrbitRepresentative f
          (sourcePlusIGaugeCurve c (t + s)) x) =
      (fun s : ℝ =>
        pairedGaugeData.fermion (sourcePlusIGaugeCurve c t)
          (actualOriginalSmoothGaugeOrbitRepresentative f
            (sourcePlusIGaugeCurve c s)
              (pairedGaugeData.boson (sourcePlusIGaugeCurve c t)⁻¹ x))) := by
    funext s
    exact actualOriginalSmoothGaugeOrbit_colorCurve_add c f t s x
  -- Unfold only the small local coordinate abbreviation, before
  -- rewriting the entire function. Keep the qualified Fock maps opaque.
  dsimp only [y] at htrans
  rw [hcurve]
  exact htrans

#print axioms actualOriginalSmoothGaugeOrbit_colorCurve_shifted_hasDerivAt_zero
#check @actualOriginalSmoothGaugeOrbit_colorCurve_shifted_hasDerivAt_zero

end
end FCP.BFSSSU2PhysicalDomainL6H5D2
