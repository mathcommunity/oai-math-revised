import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AOriginalColorCurveFullL2GaussDerivativeProbe

/-!
L6H5E8B — the TRUE original SU2 one-parameter FullL2 group has
a maximal (real-time) infinitesimal differentiability domain.
For every original source SmoothCore vector its actual embedding
belongs to this domain, and the genuine infinitesimal generator
acts there as the original source-exact color Gauss candidate.

The maximal domain is defined only by DifferentiableAt of the
actual source U_c(t) orbit at zero; no assumption is inserted
about its domain, nor is the operator arbitrarily extended to
vectors that do not have a derivative. H5E8A supplies the true
strong derivative. Source coreToL2_dense then makes the domain
dense in the original entire FullL2 Hilbert space.

The generator is represented as a partial function on a subtype
of its genuine domain. Its global linearity, skew-adjointness,
closedness, essential self-adjointness of any core restriction,
and BFSS spectral conclusions remain separate, unproved here.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8B
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6H5B
open FCP.BFSSSU2PhysicalDomainL6H5E8A

/-- The actual strong-derivative domain of the ORIGINAL source
SU2 +i one-parameter FullL2 unitary group for a color c.
It is NOT asserted to be the entire Hilbert space. -/
def actualOriginalFullL2ColorInfinitesimalDomain
    (c : ColorIndex 2) : Set (FullL2 2) :=
  {v | DifferentiableAt ℝ
    (fun t : ℝ =>
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c t) v) 0}

/-- The genuine strong (real-time) infinitesimal derivative,
defined only for vectors in its maximal differentiability domain.
This is a partial operator, not a bounded FullL2 endomorphism. -/
noncomputable def actualOriginalFullL2ColorInfinitesimalGenerator
    (c : ColorIndex 2)
    (v : actualOriginalFullL2ColorInfinitesimalDomain c) : FullL2 2 :=
  deriv (fun t : ℝ =>
    actualOriginalFullL2GaugePairCLM
      (sourcePlusIGaugeCurve c t) (v : FullL2 2)) 0

/-- Every true source SmoothCore vector lies in the maximal
real-time infinitesimal generator domain: no new premise. -/
theorem actualOriginalFullL2ColorInfinitesimalDomain_core_mem
    (c : ColorIndex 2) (f : SmoothCore 2) :
    coreToL2 f ∈ actualOriginalFullL2ColorInfinitesimalDomain c := by
  change DifferentiableAt ℝ
    (fun t : ℝ =>
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c t) (coreToL2 f)) 0
  exact (actualOriginalFullL2ColorCurve_hasDerivAt_core c f).differentiableAt

/-- IDENTIFICATION: the maximal original FullL2 infinitesimal
generator evaluated on source SmoothCore is exactly the
original 48-Majorana right-ordered color Gauss candidate. -/
theorem actualOriginalFullL2ColorInfinitesimalGenerator_core
    (c : ColorIndex 2) (f : SmoothCore 2) :
    actualOriginalFullL2ColorInfinitesimalGenerator c
      ⟨coreToL2 f, actualOriginalFullL2ColorInfinitesimalDomain_core_mem c f⟩ =
    coreToL2 (actualOriginalCoreColorGaussCandidate c f) := by
  change deriv
    (fun t : ℝ =>
      actualOriginalFullL2GaugePairCLM
        (sourcePlusIGaugeCurve c t) (coreToL2 f)) 0 =
    coreToL2 (actualOriginalCoreColorGaussCandidate c f)
  exact (actualOriginalFullL2ColorCurve_hasDerivAt_core c f).deriv

/-- The maximal original color infinitesimal-generator domain
is dense in FullL2, because the original source SmoothCore's
canonical embedding is independently proved dense, and ALL
its vectors now have a strong gauge-orbit derivative. -/
theorem actualOriginalFullL2ColorInfinitesimalDomain_dense
    (c : ColorIndex 2) :
    Dense (actualOriginalFullL2ColorInfinitesimalDomain c) := by
  have hsubset :
      Set.range (coreToL2 (N := 2)) ⊆
        actualOriginalFullL2ColorInfinitesimalDomain c := by
    rintro v ⟨f, rfl⟩
    exact actualOriginalFullL2ColorInfinitesimalDomain_core_mem c f
  -- #313: this pinned Mathlib lemma is capitalized `Dense.mono`.
  -- Its arguments are precisely subset-then-dense; keep source core unchanged.
  exact Dense.mono hsubset (coreToL2_dense (N := 2))

#print axioms actualOriginalFullL2ColorInfinitesimalDomain
#print axioms actualOriginalFullL2ColorInfinitesimalGenerator
#print axioms actualOriginalFullL2ColorInfinitesimalDomain_core_mem
#print axioms actualOriginalFullL2ColorInfinitesimalGenerator_core
#print axioms actualOriginalFullL2ColorInfinitesimalDomain_dense
#check @actualOriginalFullL2ColorInfinitesimalDomain_dense
#check @actualOriginalFullL2ColorInfinitesimalGenerator_core

end
end FCP.BFSSSU2PhysicalDomainL6H5E8B
