import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E7COriginalGaussStrongL2ResidualLimitProbe
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
L6H5E8A — the genuine original SU2 plus-i gauge orbit on source
SmoothCore has a strong FullL2 real derivative. The derivative
is precisely the source-exact right-ordered core color Gauss
candidate embedded into the actual original Hilbert space.

Mathematics: qualified H5E7C says that the ORIGINAL source
FullL2 difference-quotient residual tends to zero strongly.
The pinned Mathlib slope-zero derivative equivalence converts
that statement into an actual HasDerivAt, not merely a
pointwise derivative of an invented fiber representation.

No source Fock expansion, surrogate action, new axiom, operator
closure/essential self-adjointness or BFSS spectral assertion.
The generator operator/domain comparison is a separate target.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8A
noncomputable section

open scoped Topology
open Filter
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6H5B
open FCP.BFSSSU2PhysicalDomainL6H5E7B
open FCP.BFSSSU2PhysicalDomainL6H5E7C

/-- An abstract, normed-real-space vector difference quotient
with residual tending to zero has its asserted strong derivative
at zero. Uses pinned Mathlib's exact slope characterization.
Concrete BFSS types are absent from this proof. -/
theorem abstract_hasDerivAt_zero_of_quotientResidual_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (orbit : ℝ → E) (v : E)
    (hres : Tendsto
      (fun t : ℝ => t⁻¹ • (orbit t - orbit 0) - v)
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : E))) :
    HasDerivAt orbit v 0 := by
  have hconst :
      Tendsto (fun _ : ℝ => v)
        (𝓝[≠] (0 : ℝ)) (𝓝 v) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun t : ℝ => (t⁻¹ • (orbit t - orbit 0) - v) + v)
        (𝓝[≠] (0 : ℝ)) (𝓝 ((0 : E) + v)) :=
    hres.add hconst
  have hlim :
      Tendsto (fun t : ℝ => t⁻¹ • (orbit t - orbit 0))
        (𝓝[≠] (0 : ℝ)) (𝓝 v) := by
    simpa only [sub_add_cancel, zero_add] using hsum
  apply (hasDerivAt_iff_tendsto_slope_zero).2
  simpa only [zero_add] using hlim

/-- TRUE real-time strong FullL2 derivative of the exact original
SU2 gauge action, at original SmoothCore vectors. The derivative
is the ORIGINAL source Gauss candidate, with the +i fermion
current, inverse boson pullback sign, and right-ordered
coordinate derivative all unchanged. -/
theorem actualOriginalFullL2ColorCurve_hasDerivAt_core
    (c : ColorIndex 2) (f : SmoothCore 2) :
    HasDerivAt
      (fun t : ℝ =>
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c t) (coreToL2 f))
      (coreToL2 (actualOriginalCoreColorGaussCandidate c f)) 0 := by
  apply abstract_hasDerivAt_zero_of_quotientResidual_tendsto_zero
  exact actualOriginalGaussFullL2Residual_tendsto_zero c f

#print axioms abstract_hasDerivAt_zero_of_quotientResidual_tendsto_zero
#print axioms actualOriginalFullL2ColorCurve_hasDerivAt_core
#check @actualOriginalFullL2ColorCurve_hasDerivAt_core

end
end FCP.BFSSSU2PhysicalDomainL6H5E8A
