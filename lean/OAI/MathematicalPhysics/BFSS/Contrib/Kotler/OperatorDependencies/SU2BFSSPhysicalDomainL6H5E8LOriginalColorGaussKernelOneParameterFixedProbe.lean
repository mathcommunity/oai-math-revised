import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8KOriginalColorMaximalGeneratorClosedGraphProbe
import Mathlib.Analysis.Calculus.MeanValue

/-!
L6H5E8L — exact source original SU2 one-color infinitesimal
Gauss kernel iff true invariance under the full one-parameter
color gauge flow, for every real time.

No hidden differentiability restriction in the fixed → kernel
direction: H5E8I's qualified integral converse gives the
actual maximal domain and the exact generator value zero.
For kernel → fixed: H5E8G's qualified all-time derivative is
U_c(s) A_c v = 0, and pinned Mathlib's differentiable-vector-
orbit constant theorem gives U_c(s)v = U_c(0)v = v.

This is a substantive step toward the physical Gauss
constraint equivalence, but it is NOT YET invariance under
the entire SU(2) gauge group. A separate qualification must
prove generation of the original SU2 group by the source
color one-parameter subgroups before claiming the global
physicalSpace ↔ joint infinitesimal kernel result.

The source +i convention, inverse bosonic pullback, fiber
Fock action, maximal domain and strict axiom checks remain
unchanged. No new axioms or spectral conclusion.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8L
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6H5A
open FCP.BFSSSU2PhysicalDomainL6H5E8E
open FCP.BFSSSU2PhysicalDomainL6H5E8G
open FCP.BFSSSU2PhysicalDomainL6H5E8I

/-- Zero original maximal color Gauss generator implies
invariance under the ENTIRE associated one-parameter
source SU2 gauge subgroup, not just zero-time flatness. -/
theorem actualOriginalColorGenerator_kernel_implies_colorFlow_fixed
    (c : ColorIndex 2)
    (v : actualOriginalColorGeneratorDomainSubmodule c)
    (hv : actualOriginalColorGeneratorLinear c v = 0)
    (t : ℝ) :
    actualOriginalFullL2GaugePairCLM
      (sourcePlusIGaugeCurve c t) (v : FullL2 2) =
      (v : FullL2 2) := by
  have hdiff :
      Differentiable ℝ (fun s : ℝ =>
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c s) (v : FullL2 2)) :=
    actualOriginalColorGenerator_orbit_differentiable c v
  have hderiv : ∀ s : ℝ,
      deriv (fun r : ℝ =>
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c r) (v : FullL2 2)) s = 0 := by
    intro s
    rw [actualOriginalColorGenerator_orbit_deriv_eq c v s, hv]
    exact (actualOriginalFullL2GaugePairCLM
      (sourcePlusIGaugeCurve c s)).map_zero
  have hconst := is_const_of_deriv_eq_zero hdiff hderiv t 0
  rw [actualOriginalFullL2ColorCurve_zero] at hconst
  exact hconst

/-- Conversely, every vector genuinely fixed by the
whole original c-colored SU2 flow belongs to the EXACT
maximal domain and is annihilated by the original Gauss
generator. This does NOT require prior domain membership. -/
theorem actualOriginalColorFlow_fixed_implies_generator_kernel
    (c : ColorIndex 2) (v : FullL2 2)
    (hv : ∀ t : ℝ,
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c t) v = v) :
    ∃ hdom : v ∈ actualOriginalColorGeneratorDomainSubmodule c,
      actualOriginalColorGeneratorLinear c ⟨v, hdom⟩ = 0 := by
  have heq : ∀ t : ℝ,
      (∫ s in (0 : ℝ)..t,
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c s) (0 : FullL2 2)) =
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c t) v - v := by
    intro t
    have hfun :
        (fun s : ℝ =>
          actualOriginalFullL2GaugePairCLM
            (sourcePlusIGaugeCurve c s) (0 : FullL2 2)) =
        (fun _ : ℝ => (0 : FullL2 2)) := by
      funext s
      exact (actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c s)).map_zero
    rw [hfun]
    simp only [intervalIntegral.integral_zero, hv t, sub_self]
  exact ⟨actualOriginalColorIntegral_implies_generatorDomain
      c v 0 heq,
    actualOriginalColorIntegral_implies_generator_eq c v 0 heq⟩

/-- The genuine original BFSS color infinitesimal
kernel equals the fixed vectors of the corresponding
source plus-i one-parameter gauge subgroup. -/
theorem actualOriginalColorGenerator_kernel_iff_colorFlow_fixed
    (c : ColorIndex 2) (v : FullL2 2) :
    (∃ hdom : v ∈ actualOriginalColorGeneratorDomainSubmodule c,
      actualOriginalColorGeneratorLinear c ⟨v, hdom⟩ = 0) ↔
    (∀ t : ℝ,
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c t) v = v) := by
  constructor
  · rintro ⟨hdom, hzero⟩ t
    exact actualOriginalColorGenerator_kernel_implies_colorFlow_fixed
      c ⟨v, hdom⟩ hzero t
  · intro hfixed
    exact actualOriginalColorFlow_fixed_implies_generator_kernel
      c v hfixed

#print axioms actualOriginalColorGenerator_kernel_implies_colorFlow_fixed
#print axioms actualOriginalColorFlow_fixed_implies_generator_kernel
#print axioms actualOriginalColorGenerator_kernel_iff_colorFlow_fixed
#check @actualOriginalColorGenerator_kernel_iff_colorFlow_fixed

end
end FCP.BFSSSU2PhysicalDomainL6H5E8L
