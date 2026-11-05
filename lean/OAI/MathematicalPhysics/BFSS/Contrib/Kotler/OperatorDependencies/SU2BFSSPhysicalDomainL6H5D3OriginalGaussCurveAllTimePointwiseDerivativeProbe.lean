import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5D2OriginalGaussCurveShiftedPointwiseDerivativeProbe
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
L6H5D3 — EXACT original source color Gauss curve pointwise derivative
at every real time, not merely the parameter-shifted derivative at 0.

Use the independently qualified H5D2 shifted-source derivative,
followed by a generic (source-agnostic) Mathlib translation lemma.
The original +i SU2 curve, inverse bosonic pullback, finite
48-Majorana Fock fiber, and original SmoothCore Gauss candidate
are neither expanded nor modified.

No assertion of FullL2 norm differentiation, generator-domain
identification, self-adjointness, or a spectral theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5D3
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6H0
open FCP.BFSSSU2PhysicalDomainL6H5B
open FCP.BFSSSU2PhysicalDomainL6H5D2

/-- Real-time differentiation at a translated base point, proved
abstractly to keep the exact concrete BFSS source opaque. -/
private theorem hasDerivAt_of_shifted
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (orbit : ℝ → E) (t : ℝ) (v : E)
    (hshift : HasDerivAt (fun s : ℝ => orbit (t + s)) v 0) :
    HasDerivAt orbit v t := by
  have hstart : HasDerivAt (fun s : ℝ => orbit (t + s)) v (-t + t) := by
    simpa only [neg_add_cancel] using hshift
  have htranslated := hstart.comp_const_add (-t) t
  have hfun :
      (fun s : ℝ => orbit (t + (-t + s))) = orbit := by
    funext s
    congr 1
    ring
  change HasDerivAt (fun s : ℝ => orbit (t + (-t + s))) v t at htranslated
  rw [hfun] at htranslated
  exact htranslated

/-- Genuine source SU2 pointwise color Gauss-orbit derivative
at EVERY real time, with the original fermionic isometry and
bosonic inverse gauge action. This remains a pointwise theorem. -/
theorem actualOriginalSmoothGaugeOrbit_colorCurve_hasDerivAt
    (c : ColorIndex 2) (f : SmoothCore 2)
    (t : ℝ) (x : Boson 2) :
    HasDerivAt
      (fun s : ℝ =>
        actualOriginalSmoothGaugeOrbitRepresentative f
          (sourcePlusIGaugeCurve c s) x)
      (pairedGaugeData.fermion (sourcePlusIGaugeCurve c t)
        ((actualOriginalCoreColorGaussCandidate c f)
          (pairedGaugeData.boson (sourcePlusIGaugeCurve c t)⁻¹ x)))
      t := by
  exact hasDerivAt_of_shifted
    (fun s : ℝ =>
      actualOriginalSmoothGaugeOrbitRepresentative f
        (sourcePlusIGaugeCurve c s) x) t
    (pairedGaugeData.fermion (sourcePlusIGaugeCurve c t)
      ((actualOriginalCoreColorGaussCandidate c f)
        (pairedGaugeData.boson (sourcePlusIGaugeCurve c t)⁻¹ x)))
    (actualOriginalSmoothGaugeOrbit_colorCurve_shifted_hasDerivAt_zero
      c f t x)

#print axioms actualOriginalSmoothGaugeOrbit_colorCurve_hasDerivAt
#check @actualOriginalSmoothGaugeOrbit_colorCurve_hasDerivAt

end
end FCP.BFSSSU2PhysicalDomainL6H5D3
