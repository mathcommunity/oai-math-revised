import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8BOriginalColorInfinitesimalGeneratorDomainProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7ZActualSourceFullL2UnitaryGaugeRepresentationProbe
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
L6H5E8C — original source color Gauss infinitesimal generator
is skew-symmetric on the genuine BFSS SmoothCore, after canonical
embedding into the actual FullL2 Hilbert space.

The original +i SU2 gauge action is exactly the previously-qualified
unitary source representation (L6G7Z). Its core strong derivatives
are exactly H5E8A. The abstract result differentiates the constant
Hilbert inner product of two unitary orbits and forces the sum of
the derivative inner products to vanish.

No surrogate Fock model, source sign change, new axiom, core
essential self-adjointness, global generator closedness, or
spectral claim. This is skew-symmetry ON SmoothCore only.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8C
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6G7Z
open FCP.BFSSSU2PhysicalDomainL6H5A
open FCP.BFSSSU2PhysicalDomainL6H5B
open FCP.BFSSSU2PhysicalDomainL6H5E8A

/-- An abstract differentiable unitary orbit has a skew-symmetric
derivative at the identity. Pinned Mathlib supplies both the
Hilbert inner derivative and unitary inner preservation. -/
theorem abstract_unitary_orbit_derivatives_skew
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedSpace ℝ E]
    (U : ℝ → E ≃ₗᵢ[ℂ] E)
    (u v du dv : E)
    (h0u : U 0 u = u) (h0v : U 0 v = v)
    (hu : HasDerivAt (fun t : ℝ => U t u) du 0)
    (hv : HasDerivAt (fun t : ℝ => U t v) dv 0) :
    inner ℂ u dv + inner ℂ du v = 0 := by
  have hderiv :
      HasDerivAt (fun t : ℝ => inner ℂ (U t u) (U t v))
        (inner ℂ (U 0 u) dv + inner ℂ du (U 0 v)) 0 :=
    hu.inner ℂ hv
  have hinner : (fun t : ℝ => inner ℂ (U t u) (U t v)) =
      (fun _ : ℝ => inner ℂ u v) := by
    funext t
    exact (U t).inner_map_map u v
  have hzero :
      HasDerivAt (fun t : ℝ => inner ℂ (U t u) (U t v))
        (0 : ℂ) 0 := by
    rw [hinner]
    exact hasDerivAt_const 0 (inner ℂ u v)
  have hident := hderiv.unique hzero
  simpa only [h0u, h0v] using hident

/-- Source-EXACT original BFSS color Gauss candidate, represented
on original SmoothCore then embedded in genuine FullL2, is
skew-symmetric with the original complex Hilbert inner product. -/
theorem actualOriginalCoreColorGaussCandidate_skew_inner
    (c : ColorIndex 2) (f g : SmoothCore 2) :
    inner ℂ (coreToL2 f)
        (coreToL2 (actualOriginalCoreColorGaussCandidate c g)) +
      inner ℂ (coreToL2 (actualOriginalCoreColorGaussCandidate c f))
        (coreToL2 g) = 0 := by
  let U : ℝ → FullL2 2 ≃ₗᵢ[ℂ] FullL2 2 :=
    fun t => actualOriginalFullL2GaugeUnitaryEquiv
      (sourcePlusIGaugeCurve c t)
  have h0u : U 0 (coreToL2 f) = coreToL2 f := by
    change actualOriginalFullL2GaugePairCLM
      (sourcePlusIGaugeCurve c 0) (coreToL2 f) = coreToL2 f
    exact actualOriginalFullL2ColorCurve_zero c (coreToL2 f)
  have h0v : U 0 (coreToL2 g) = coreToL2 g := by
    change actualOriginalFullL2GaugePairCLM
      (sourcePlusIGaugeCurve c 0) (coreToL2 g) = coreToL2 g
    exact actualOriginalFullL2ColorCurve_zero c (coreToL2 g)
  have hdu :
      HasDerivAt (fun t : ℝ => U t (coreToL2 f))
        (coreToL2 (actualOriginalCoreColorGaussCandidate c f)) 0 := by
    change HasDerivAt
      (fun t : ℝ =>
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c t) (coreToL2 f))
      (coreToL2 (actualOriginalCoreColorGaussCandidate c f)) 0
    exact actualOriginalFullL2ColorCurve_hasDerivAt_core c f
  have hdv :
      HasDerivAt (fun t : ℝ => U t (coreToL2 g))
        (coreToL2 (actualOriginalCoreColorGaussCandidate c g)) 0 := by
    change HasDerivAt
      (fun t : ℝ =>
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c t) (coreToL2 g))
      (coreToL2 (actualOriginalCoreColorGaussCandidate c g)) 0
    exact actualOriginalFullL2ColorCurve_hasDerivAt_core c g
  exact abstract_unitary_orbit_derivatives_skew
    U (coreToL2 f) (coreToL2 g)
    (coreToL2 (actualOriginalCoreColorGaussCandidate c f))
    (coreToL2 (actualOriginalCoreColorGaussCandidate c g))
    h0u h0v hdu hdv

#print axioms abstract_unitary_orbit_derivatives_skew
#print axioms actualOriginalCoreColorGaussCandidate_skew_inner
#check @actualOriginalCoreColorGaussCandidate_skew_inner

end
end FCP.BFSSSU2PhysicalDomainL6H5E8C
