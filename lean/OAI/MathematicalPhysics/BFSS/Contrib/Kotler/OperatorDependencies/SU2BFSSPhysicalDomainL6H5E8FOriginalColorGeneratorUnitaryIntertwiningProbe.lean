import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8EOriginalColorMaximalGeneratorComplexLinearityProbe
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
L6H5E8F — the EXACT original SU2 color unitary flow preserves
the maximal domain of its strong infinitesimal generator, and
the genuine complex-linear generator COMMUTES with that flow
on the domain.

Accepted inputs: H5E8E true complex-linear maximal domain and
source Gauss action; H5A actual source plus-i one-parameter
group law; H5E8D derivative on its full maximal domain; pinned
Mathlib bounded real-linear chain rule.

We abstract CLM composition and the commuting additive
one-parameter action BEFORE specializing to 48-Majorana
BFSS, avoiding high-cost Fock-operator elaboration.

NO assertion of closedness, essential skew-adjointness,
equality of physical and joint infinitesimal kernels, or
spectral conclusions. No source sign, action, pin or axiom
changes.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8F
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6H5A
open FCP.BFSSSU2PhysicalDomainL6H5E8B
open FCP.BFSSSU2PhysicalDomainL6H5E8D
open FCP.BFSSSU2PhysicalDomainL6H5E8E

/-- Entirely abstract one-parameter CLM group law transports
a strong orbit derivative at zero through an arbitrary fixed
group time. The complex CLM is restricted to REAL scalars only
for the real-time chain rule. -/
theorem abstract_additive_CLM_group_orbit_derivative
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (U : ℝ → E →L[ℂ] E)
    (hadd : ∀ (s t : ℝ) (v : E),
      U (s + t) v = U s (U t v))
    (s : ℝ) (v dv : E)
    (hv : HasDerivAt (fun t : ℝ => U t v) dv 0) :
    HasDerivAt (fun t : ℝ => U t (U s v)) (U s dv) 0 := by
  let L : E →L[ℝ] E := (U s).restrictScalars ℝ
  have hpost :
      HasDerivAt (fun t : ℝ => L (U t v)) (L dv) 0 := by
    have hcomp :=
      -- #320/#321: CLM.hasFDerivAt's point is implicit, but the
      -- pinned chain rule comp_hasDerivAt takes real-time x explicitly.
      (L.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hv
    simpa only [Function.comp_def] using hcomp
  have heq :
      (fun t : ℝ => U t (U s v)) =
      (fun t : ℝ => L (U t v)) := by
    funext t
    calc
      U t (U s v) = U (t + s) v := (hadd t s v).symm
      _ = U (s + t) v := by rw [add_comm]
      _ = U s (U t v) := hadd s t v
      _ = L (U t v) := rfl
  rw [heq]
  exact hpost

/-- For every original color c, real time s, and vector on
the exact maximal generator domain, the ORIGINAL SU2 gauge
orbit of its translated vector has strong derivative
U_c(s) A_c v, with unchanged source definitions. -/
theorem actualOriginalColorGenerator_shifted_hasDerivAt
    (c : ColorIndex 2) (s : ℝ)
    (v : actualOriginalColorGeneratorDomainSubmodule c) :
    HasDerivAt
      (fun t : ℝ =>
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c t)
          (actualOriginalFullL2GaugePairCLM
            (sourcePlusIGaugeCurve c s) (v : FullL2 2)))
      (actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c s)
        (actualOriginalColorGeneratorLinear c v)) 0 := by
  let U : ℝ → FullL2 2 →L[ℂ] FullL2 2 :=
    fun t => actualOriginalFullL2GaugePairCLM
      (sourcePlusIGaugeCurve c t)
  have hgroup : ∀ (a b : ℝ) (w : FullL2 2),
      U (a + b) w = U a (U b w) := by
    intro a b w
    exact actualOriginalFullL2ColorCurve_add c a b w
  have hv : HasDerivAt (fun t : ℝ => U t (v : FullL2 2))
      (actualOriginalColorGeneratorLinear c v) 0 := by
    change HasDerivAt
      (fun t : ℝ =>
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c t) (v : FullL2 2))
      (actualOriginalFullL2ColorInfinitesimalGenerator c
        ⟨(v : FullL2 2), v.property⟩) 0
    exact actualOriginalColorGenerator_hasDerivAt c
      ⟨(v : FullL2 2), v.property⟩
  exact abstract_additive_CLM_group_orbit_derivative
    U hgroup s (v : FullL2 2)
    (actualOriginalColorGeneratorLinear c v) hv

/-- Source original SU2 color orbit leaves its exact
maximal strong differentiability domain invariant. -/
theorem actualOriginalColorGenerator_domain_invariant
    (c : ColorIndex 2) (s : ℝ)
    (v : actualOriginalColorGeneratorDomainSubmodule c) :
    actualOriginalFullL2GaugePairCLM
      (sourcePlusIGaugeCurve c s) (v : FullL2 2) ∈
      actualOriginalColorGeneratorDomainSubmodule c := by
  change DifferentiableAt ℝ
    (fun t : ℝ =>
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c t)
        (actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c s) (v : FullL2 2))) 0
  exact (actualOriginalColorGenerator_shifted_hasDerivAt c s v).differentiableAt

/-- Full original source generator intertwines with every
element of its own color one-parameter unitary group:
A_c(U_c(s)v) = U_c(s)(A_c v), on the MAXIMAL domain. -/
theorem actualOriginalColorGenerator_intertwines
    (c : ColorIndex 2) (s : ℝ)
    (v : actualOriginalColorGeneratorDomainSubmodule c) :
    actualOriginalColorGeneratorLinear c
      ⟨actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c s) (v : FullL2 2),
        actualOriginalColorGenerator_domain_invariant c s v⟩ =
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c s)
        (actualOriginalColorGeneratorLinear c v) := by
  change deriv
    (fun t : ℝ =>
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c t)
        (actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c s) (v : FullL2 2))) 0 =
    actualOriginalFullL2GaugePairCLM
      (sourcePlusIGaugeCurve c s)
      (actualOriginalColorGeneratorLinear c v)
  exact (actualOriginalColorGenerator_shifted_hasDerivAt c s v).deriv

#print axioms abstract_additive_CLM_group_orbit_derivative
#print axioms actualOriginalColorGenerator_shifted_hasDerivAt
#print axioms actualOriginalColorGenerator_domain_invariant
#print axioms actualOriginalColorGenerator_intertwines
#check @actualOriginalColorGenerator_intertwines

end
end FCP.BFSSSU2PhysicalDomainL6H5E8F
