import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E3OriginalGaussOrbitDifferenceQuotientEnvelopeProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5C3OriginalGaussCandidatePointwiseDerivativeBridgeProbe
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
L6H5E4 — EXACT original source BFSS color Gauss difference quotients
converge pointwise to the source SmoothCore Gauss candidate as
real t approaches zero through nonzero values.

The quotient is the actual source Fock-fiber REAL scalar inverse
acting on the difference of original +i SU2 smooth gauge orbits.
The only derivative input is H5C3's qualified ORIGINAL pointwise
derivative, converted by pinned Mathlib's slope-zero characterization.

H5E3 already proves a single squared-integrable envelope for the
same nonzero-time quotient. Pointwise convergence here is not yet
the FullL2 dominated-convergence limit or a generator-domain theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E4
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6H0
open FCP.BFSSSU2PhysicalDomainL6H5B
open FCP.BFSSSU2PhysicalDomainL6H5C3
-- CI #292: the punctured-neighborhood notation 𝓝[≠] is in the
-- Topology notation scope of pinned Mathlib Deriv/Slope, not activated
-- by merely opening the Filter namespace. Both theorem parse failures
-- and subsequent unknown identifiers were downstream of this omission.
open scoped Topology
open Filter

/-- A purely vector-valued real derivative entails a punctured-zero
difference-quotient limit. Concrete source gauge internals remain
opaque when we later specialize this mathematical statement. -/
theorem tendsto_punctured_differenceQuotient_of_hasDerivAt_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (orbit : ℝ → E) (v : E)
    (hd : HasDerivAt orbit v 0) :
    Tendsto (fun t : ℝ => t⁻¹ • (orbit t - orbit 0))
      (𝓝[≠] (0 : ℝ)) (𝓝 v) := by
  simpa only [zero_add] using hd.tendsto_slope_zero

/-- At every actual bosonic configuration, the original real time
difference quotient of the exact +i gauge orbit converges to the
source-exact Gauss candidate on the original Fock fiber. -/
theorem actualOriginalGaussOrbit_differenceQuotient_pointwise_tendsto
    (c : ColorIndex 2) (f : SmoothCore 2) (x : Boson 2) :
    Tendsto
      (fun t : ℝ =>
        t⁻¹ •
          (actualOriginalSmoothGaugeOrbitRepresentative f
              (sourcePlusIGaugeCurve c t) x -
            actualOriginalSmoothGaugeOrbitRepresentative f
              (sourcePlusIGaugeCurve c 0) x))
      (𝓝[≠] (0 : ℝ))
      (𝓝 ((actualOriginalCoreColorGaussCandidate c f) x)) := by
  have hd :=
    actualOriginalSmoothGaugeOrbit_gaussCandidate_pointwise_derivative_zero c f x
  exact tendsto_punctured_differenceQuotient_of_hasDerivAt_zero
    (fun t : ℝ =>
      actualOriginalSmoothGaugeOrbitRepresentative f
        (sourcePlusIGaugeCurve c t) x)
    ((actualOriginalCoreColorGaussCandidate c f) x) hd

#print axioms tendsto_punctured_differenceQuotient_of_hasDerivAt_zero
#print axioms actualOriginalGaussOrbit_differenceQuotient_pointwise_tendsto
#check @tendsto_punctured_differenceQuotient_of_hasDerivAt_zero
#check @actualOriginalGaussOrbit_differenceQuotient_pointwise_tendsto

end
end FCP.BFSSSU2PhysicalDomainL6H5E4
