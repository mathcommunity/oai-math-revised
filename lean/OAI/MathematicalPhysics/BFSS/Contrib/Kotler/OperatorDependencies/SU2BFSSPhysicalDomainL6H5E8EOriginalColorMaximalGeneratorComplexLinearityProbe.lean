import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8DOriginalMaximalGaussSkewAndPhysicalKernelProbe
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
H5E8E — original BFSS maximal real-time source color generator
has EXACT complex-linear domain and action. H5E8B/H5E8D
supply the genuine derivative; the original gauge operator
is complex linear at each t. No proxy action, assumptions,
altered +i signs, closure, or self-adjointness claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8E
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6H5B
open FCP.BFSSSU2PhysicalDomainL6H5E8B
open FCP.BFSSSU2PhysicalDomainL6H5E8D

private noncomputable def exactColorU (c : ColorIndex 2) (t : ℝ) :
    FullL2 2 →L[ℂ] FullL2 2 :=
  actualOriginalFullL2GaugePairCLM (sourcePlusIGaugeCurve c t)

/-- Exactly the original maximal differentiability domain,
now proved a complex linear subspace. -/
noncomputable def actualOriginalColorGeneratorDomainSubmodule
    (c : ColorIndex 2) : Submodule ℂ (FullL2 2) where
  carrier := actualOriginalFullL2ColorInfinitesimalDomain c
  zero_mem' := by
    change DifferentiableAt ℝ
      (fun t : ℝ => exactColorU c t (0 : FullL2 2)) 0
    have h : (fun t : ℝ => exactColorU c t (0 : FullL2 2)) =
        (fun _ : ℝ => (0 : FullL2 2)) := by
      funext t
      exact (exactColorU c t).map_zero
    rw [h]
    exact (hasDerivAt_const 0 (0 : FullL2 2)).differentiableAt
  add_mem' := by
    intro u v hu hv
    change DifferentiableAt ℝ (fun t : ℝ => exactColorU c t (u + v)) 0
    have hdu : DifferentiableAt ℝ (fun t : ℝ => exactColorU c t u) 0 := hu
    have hdv : DifferentiableAt ℝ (fun t : ℝ => exactColorU c t v) 0 := hv
    have h : (fun t : ℝ => exactColorU c t (u + v)) =
        (fun t : ℝ => exactColorU c t u + exactColorU c t v) := by
      funext t
      exact (exactColorU c t).map_add u v
    rw [h]
    exact hdu.add hdv
  smul_mem' := by
    intro a v hv
    change DifferentiableAt ℝ (fun t : ℝ => exactColorU c t (a • v)) 0
    have hdv : DifferentiableAt ℝ (fun t : ℝ => exactColorU c t v) 0 := hv
    have h : (fun t : ℝ => exactColorU c t (a • v)) =
        (fun t : ℝ => a • exactColorU c t v) := by
      funext t
      exact (exactColorU c t).map_smul a v
    rw [h]
    exact (hdv.hasDerivAt.const_smul a).differentiableAt

theorem actualOriginalColorGeneratorDomainSubmodule_mem
    (c : ColorIndex 2) (v : FullL2 2) :
    v ∈ actualOriginalColorGeneratorDomainSubmodule c ↔
      v ∈ actualOriginalFullL2ColorInfinitesimalDomain c := Iff.rfl

/-- The original unbounded-domain infinitesimal generator,
as an actual complex linear map on exactly its natural domain. -/
noncomputable def actualOriginalColorGeneratorLinear
    (c : ColorIndex 2) :
    actualOriginalColorGeneratorDomainSubmodule c →ₗ[ℂ] FullL2 2 where
  toFun := fun v => actualOriginalFullL2ColorInfinitesimalGenerator c
    ⟨(v : FullL2 2), v.property⟩
  map_add' := by
    intro x y
    change deriv (fun t : ℝ =>
        exactColorU c t ((x : FullL2 2) + (y : FullL2 2))) 0 =
      deriv (fun t : ℝ => exactColorU c t (x : FullL2 2)) 0 +
      deriv (fun t : ℝ => exactColorU c t (y : FullL2 2)) 0
    have hx := actualOriginalColorGenerator_hasDerivAt c
      (⟨(x : FullL2 2), x.property⟩ :
        actualOriginalFullL2ColorInfinitesimalDomain c)
    have hy := actualOriginalColorGenerator_hasDerivAt c
      (⟨(y : FullL2 2), y.property⟩ :
        actualOriginalFullL2ColorInfinitesimalDomain c)
    have h : (fun t : ℝ =>
        exactColorU c t ((x : FullL2 2) + (y : FullL2 2))) =
      (fun t : ℝ =>
        exactColorU c t (x : FullL2 2) + exactColorU c t (y : FullL2 2)) := by
      funext t
      exact (exactColorU c t).map_add _ _
    have hs := hx.add hy
    -- #318: HasDerivAt.add initially produces Pi-function addition.
    -- Expose its pointwise application before rewriting by h.
    change HasDerivAt
      (fun t : ℝ =>
        exactColorU c t (x : FullL2 2) +
        exactColorU c t (y : FullL2 2))
      (actualOriginalFullL2ColorInfinitesimalGenerator c
        ⟨(x : FullL2 2), x.property⟩ +
       actualOriginalFullL2ColorInfinitesimalGenerator c
        ⟨(y : FullL2 2), y.property⟩) 0 at hs
    rw [← h] at hs
    exact hs.deriv
  map_smul' := by
    intro a x
    change deriv (fun t : ℝ =>
        exactColorU c t (a • (x : FullL2 2))) 0 =
      a • deriv (fun t : ℝ => exactColorU c t (x : FullL2 2)) 0
    have hx := actualOriginalColorGenerator_hasDerivAt c
      (⟨(x : FullL2 2), x.property⟩ :
        actualOriginalFullL2ColorInfinitesimalDomain c)
    have h : (fun t : ℝ =>
        exactColorU c t (a • (x : FullL2 2))) =
      (fun t : ℝ => a • exactColorU c t (x : FullL2 2)) := by
      funext t
      exact (exactColorU c t).map_smul a _
    have hs := hx.const_smul a
    change HasDerivAt
      (fun t : ℝ => a • exactColorU c t (x : FullL2 2))
      (a • actualOriginalFullL2ColorInfinitesimalGenerator c
        ⟨(x : FullL2 2), x.property⟩) 0 at hs
    rw [← h] at hs
    exact hs.deriv

theorem actualOriginalColorGeneratorLinear_core
    (c : ColorIndex 2) (f : SmoothCore 2) :
    actualOriginalColorGeneratorLinear c
      ⟨coreToL2 f, actualOriginalFullL2ColorInfinitesimalDomain_core_mem c f⟩ =
    coreToL2 (actualOriginalCoreColorGaussCandidate c f) := by
  exact actualOriginalFullL2ColorInfinitesimalGenerator_core c f

#print axioms actualOriginalColorGeneratorDomainSubmodule
#print axioms actualOriginalColorGeneratorDomainSubmodule_mem
#print axioms actualOriginalColorGeneratorLinear
#print axioms actualOriginalColorGeneratorLinear_core
#check @actualOriginalColorGeneratorLinear_core

end
end FCP.BFSSSU2PhysicalDomainL6H5E8E
