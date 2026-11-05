import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7NActualBosonGaugeVectorDerivativeProbe

/-!
L6G7O — the derivative of the ORIGINAL bosonic gauge pullback on
the actual SmoothCore 2, evaluated at a physical configuration.

The pinned GaugeCore defines bosonPullback via f(g • x), not
f(g⁻¹ • x). This theorem differentiates that forward source action
on test functions, preserving the +i curve and original color tangent.
The source TestFunction smoothness supplies the Frechet derivative.
No replacement Fock space, Gauss-domain assumption, L² differentiated
pullback, closed operator assertion or spectral conclusion is used.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G7O
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG2A
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7N

/-- Pointwise derivative of the literal forward bosonic gauge pullback
on the original Schwartz-like SmoothCore. In particular no inverse
of the source SU(2) curve and no sign change is introduced. -/
theorem actualBosonGauge_smoothCore_pullback_derivative_zero
    (c : ColorIndex 2) (f : SmoothCore 2) (x : Boson 2) :
    HasDerivAt
      (fun t : ℝ => f (bosonGauge (sourcePlusIGaugeCurve c t) x))
      (fderiv ℝ (f : Boson 2 → Fermion 2) x
        (sourceBosonGaugeTangent c x)) 0 := by
  have hf :
      HasFDerivAt (f : Boson 2 → Fermion 2)
        (fderiv ℝ (f : Boson 2 → Fermion 2) x) x :=
    (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  -- The exact source +i curve starts at the identity; this is the
  -- basepoint equality required by Mathlib's composition theorem.
  have hzero : x = bosonGauge (sourcePlusIGaugeCurve c 0) x := by
    rw [sourcePlusIGaugeCurve_one]
    change x = pairedAlgebraData.gaugeConjugate (1 : ColorMatrix 2) x
    exact (pairedAlgebraData.gaugeConjugate_one x).symm
  -- Pinned Mathlib declares (x) as an explicit section variable:
  -- BOTH comp_hasDerivAt and comp_hasDerivAt_of_eq need the time 0
  -- before the inner derivative; #216 established the exact basepoint.
  simpa only [Function.comp_def] using
    hf.comp_hasDerivAt_of_eq 0
      (actualBosonGauge_vector_derivative_zero c x) hzero

#print axioms actualBosonGauge_smoothCore_pullback_derivative_zero
#check @actualBosonGauge_smoothCore_pullback_derivative_zero

end
end FCP.BFSSSU2PhysicalDomainL6G7O
