import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8FOriginalColorGeneratorUnitaryIntertwiningProbe
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
L6H5E8G — the actual ORIGINAL BFSS SU2 color maximal-domain
orbit has the real-time Hilbert-space derivative at EVERY real
time s, equal to the ORIGINAL source unitary applied to the
actual generator A_c v. Consequently the orbit is everywhere
differentiable and its derivative is norm-continuous in s.

This directly prepares the integral equation required for
closedness of the maximal generator graph.

Inputs: H5E8F true generator-domain invariance and shifted
strong derivative at time zero, H5A genuine all-vector orbit
continuity and group law, pinned Mathlib derivative-of-shift.
No Fock surrogate, changed source +i convention, new axiom,
closed-graph theorem or spectral inference.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8G
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6H5A
open FCP.BFSSSU2PhysicalDomainL6H5E8E
open FCP.BFSSSU2PhysicalDomainL6H5E8F

/-- True original source FullL2 color gauge orbit has strong
real-time derivative at EVERY time s, without another
smoothness hypothesis on v beyond maximal-domain membership. -/
theorem actualOriginalColorGenerator_orbit_hasDerivAt_allTime
    (c : ColorIndex 2)
    (v : actualOriginalColorGeneratorDomainSubmodule c)
    (s : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c t) (v : FullL2 2))
      (actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c s)
        (actualOriginalColorGeneratorLinear c v)) s := by
  let U : ℝ → FullL2 2 →L[ℂ] FullL2 2 :=
    fun t => actualOriginalFullL2GaugePairCLM
      (sourcePlusIGaugeCurve c t)
  let Av : FullL2 2 := actualOriginalColorGeneratorLinear c v
  have hzero :
      HasDerivAt
        (fun t : ℝ => U t (U s (v : FullL2 2)))
        (U s Av) 0 := by
    exact actualOriginalColorGenerator_shifted_hasDerivAt c s v
  have hat :
      HasDerivAt
        (fun t : ℝ => U t (U s (v : FullL2 2)))
        (U s Av) (s + (-s)) := by
    simpa only [add_neg_cancel] using hzero
  have htranslated := hat.comp_add_const s (-s)
  change HasDerivAt
    (fun t : ℝ => U (t + (-s)) (U s (v : FullL2 2)))
    (U s Av) s at htranslated
  have horbit :
      (fun t : ℝ => U (t + (-s)) (U s (v : FullL2 2))) =
      (fun t : ℝ => U t (v : FullL2 2)) := by
    funext t
    calc
      U (t + (-s)) (U s (v : FullL2 2)) =
          U ((t + (-s)) + s) (v : FullL2 2) :=
        (actualOriginalFullL2ColorCurve_add c (t + (-s)) s
          (v : FullL2 2)).symm
      _ = U t (v : FullL2 2) := by
        -- #323: never use `congr 1` on the concrete BFSS operator;
        -- it unfolds enormous source definitions in whnf.
        have ht : (t + (-s)) + s = t := by ring
        exact congrArg (fun q : ℝ => U q (v : FullL2 2)) ht
  rw [horbit] at htranslated
  exact htranslated

/-- Every maximal-domain vector has a real-differentiable
true original unitary color orbit on the entire real line. -/
theorem actualOriginalColorGenerator_orbit_differentiable
    (c : ColorIndex 2)
    (v : actualOriginalColorGeneratorDomainSubmodule c) :
    Differentiable ℝ (fun t : ℝ =>
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c t) (v : FullL2 2)) := by
  intro s
  exact (actualOriginalColorGenerator_orbit_hasDerivAt_allTime c v s).differentiableAt

/-- The derivative is EXACTLY the original unitary flow
applied to the original complex-linear Gauss generator,
not an unspecified or surrogate derivative. -/
theorem actualOriginalColorGenerator_orbit_deriv_eq
    (c : ColorIndex 2)
    (v : actualOriginalColorGeneratorDomainSubmodule c)
    (s : ℝ) :
    deriv (fun t : ℝ =>
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c t) (v : FullL2 2)) s =
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c s)
        (actualOriginalColorGeneratorLinear c v) := by
  exact (actualOriginalColorGenerator_orbit_hasDerivAt_allTime c v s).deriv

/-- The original maximal-domain color orbit has a CONTINUOUS
strong derivative, using independently accepted all-vector
gauge-orbit norm continuity H5A. -/
theorem actualOriginalColorGenerator_orbit_deriv_continuous
    (c : ColorIndex 2)
    (v : actualOriginalColorGeneratorDomainSubmodule c) :
    Continuous (fun s : ℝ =>
      deriv (fun t : ℝ =>
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c t) (v : FullL2 2)) s) := by
  have heq :
      (fun s : ℝ =>
        deriv (fun t : ℝ =>
          actualOriginalFullL2GaugePairCLM
            (sourcePlusIGaugeCurve c t) (v : FullL2 2)) s) =
      (fun s : ℝ =>
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c s)
          (actualOriginalColorGeneratorLinear c v)) := by
    funext s
    exact actualOriginalColorGenerator_orbit_deriv_eq c v s
  rw [heq]
  exact actualOriginalFullL2ColorCurve_orbit_continuous c
    (actualOriginalColorGeneratorLinear c v)

#print axioms actualOriginalColorGenerator_orbit_hasDerivAt_allTime
#print axioms actualOriginalColorGenerator_orbit_differentiable
#print axioms actualOriginalColorGenerator_orbit_deriv_eq
#print axioms actualOriginalColorGenerator_orbit_deriv_continuous
#check @actualOriginalColorGenerator_orbit_hasDerivAt_allTime
#check @actualOriginalColorGenerator_orbit_deriv_continuous

end
end FCP.BFSSSU2PhysicalDomainL6H5E8G
