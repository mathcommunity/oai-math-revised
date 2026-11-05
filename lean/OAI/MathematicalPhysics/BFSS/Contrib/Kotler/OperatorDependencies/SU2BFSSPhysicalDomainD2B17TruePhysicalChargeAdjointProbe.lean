import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B16PhysicalHilbertRebasedChargeOperatorProbe
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# BFSS SU2 D2B17 — genuine Hilbert-valued physical charge adjoint

PROSPECTIVE until the exact pinned compiler and axiom gate passes.

Source G.deformedModelGraph 1 0 is transported:
* input: original source G.physicalSpace (Gate D2B16);
* output: PiLp 2 sixteen original FullL2 components.

This is the mathematically required finite L² Hilbert sum.
The original source output type SpinIndex → FullL2 has the finite
product/sup norm and therefore lacks a Hilbert inner-product instance.
The pinned PiLp.continuousLinearEquiv is an exact homeomorphic
ℂ-linear identification, NOT an added physical axiom or an invented
operator. Graph membership, closedness and physical-domain density
are proved prior to using Mathlib's unbounded Hilbert adjoint.

This is a charge-column adjoint, NOT a self-adjoint Hamiltonian or
manuscript operator identification. No spectral claims follow.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B17
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2B16
open MeasureTheory Set
open scoped InnerProductSpace

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- True sixteen-component Hilbert direct sum with the ℓ² norm. -/
abbrev SourceChargeHilbertOutput :=
  PiLp 2 (fun _ : SpinIndex => FullL2 2)

/-- The exact pinned continuous linear equivalence between Hilbert
ℓ² outputs and the original sixteen component source output type. -/
noncomputable def sourceChargeOutputHilbertEquiv :
    SourceChargeHilbertOutput ≃L[ℂ] (SpinIndex → FullL2 2) :=
  PiLp.continuousLinearEquiv 2 ℂ (fun _ : SpinIndex => FullL2 2)

/-- Source physical charge graph with the output carried by the
correct sixteen-component Hilbert direct sum. -/
noncomputable def sourcePhysicalHilbertChargeGraph :
    Submodule ℂ (G.physicalSpace × SourceChargeHilbertOutput) :=
  (sourcePhysicalRebasedChargeGraph M G).comap
    ((LinearMap.id : G.physicalSpace →ₗ[ℂ] G.physicalSpace).prodMap
      (sourceChargeOutputHilbertEquiv).toLinearMap)

/-- Every graph point maps EXACTLY to the original source physical
charge graph under the canonical L² Hilbert-output identification. -/
theorem sourcePhysicalHilbertChargeGraph_mem_iff
    (p : G.physicalSpace × SourceChargeHilbertOutput) :
    p ∈ sourcePhysicalHilbertChargeGraph M G ↔
      (p.1, sourceChargeOutputHilbertEquiv p.2) ∈
        sourcePhysicalRebasedChargeGraph M G := by
  rfl

private theorem sourcePhysicalHilbertChargeGraph_vertical :
    ∀ (p : G.physicalSpace × SourceChargeHilbertOutput),
      p ∈ sourcePhysicalHilbertChargeGraph M G →
      p.1 = 0 → p.2 = 0 := by
  rintro ⟨ψ,y⟩ hp hz
  have hrebased :
      (ψ,sourceChargeOutputHilbertEquiv y) ∈
        sourcePhysicalRebasedChargeGraph M G :=
    (sourcePhysicalHilbertChargeGraph_mem_iff M G _).mp hp
  have horiginal :
      ((ψ : FullL2 2), sourceChargeOutputHilbertEquiv y) ∈
        G.deformedModelGraph 1 0 :=
    (sourcePhysicalRebasedChargeGraph_mem_iff M G _).mp hrebased
  have hz' : (ψ : FullL2 2) = 0 :=
    congrArg (fun x : G.physicalSpace => (x : FullL2 2)) hz
  have hzero : ((0 : FullL2 2), sourceChargeOutputHilbertEquiv y) ∈
      G.deformedModelGraph 1 0 := by
    simpa only [hz'] using horiginal
  have hy : sourceChargeOutputHilbertEquiv y = 0 :=
    G.deformedModelGraph_vertical 1 0 hzero
  apply (sourceChargeOutputHilbertEquiv).injective
  simpa using hy

/-- Genuine Mathlib ℂ-linear partially-defined charge operator from
the ORIGINAL source graph, now with both true Hilbert ambient spaces. -/
noncomputable def sourcePhysicalHilbertChargeColumn :
    G.physicalSpace →ₗ.[ℂ] SourceChargeHilbertOutput :=
  (sourcePhysicalHilbertChargeGraph M G).toLinearPMap

theorem sourcePhysicalHilbertChargeColumn_graph_eq :
    (sourcePhysicalHilbertChargeColumn M G).graph =
      sourcePhysicalHilbertChargeGraph M G := by
  exact Submodule.toLinearPMap_graph_eq _
    (sourcePhysicalHilbertChargeGraph_vertical M G)

/-- Closedness transfers through Mathlib's continuous linear
equivalence, so the transported graph is the literal source graph. -/
theorem sourcePhysicalHilbertChargeColumn_isClosed :
    (sourcePhysicalHilbertChargeColumn M G).IsClosed := by
  change IsClosed ((sourcePhysicalHilbertChargeColumn M G).graph :
    Set (G.physicalSpace × SourceChargeHilbertOutput))
  rw [sourcePhysicalHilbertChargeColumn_graph_eq M G]
  change IsClosed {p : G.physicalSpace × SourceChargeHilbertOutput |
    (p.1,sourceChargeOutputHilbertEquiv p.2) ∈
      (sourcePhysicalRebasedChargeGraph M G :
        Set (G.physicalSpace × (SpinIndex → FullL2 2)))}
  have hclosed : IsClosed (sourcePhysicalRebasedChargeGraph M G :
      Set (G.physicalSpace × (SpinIndex → FullL2 2))) := by
    rw [← sourcePhysicalRebasedChargeColumn_graph_eq M G]
    exact sourcePhysicalRebasedChargeColumn_isClosed M G
  have hcont : Continuous
      (fun p : G.physicalSpace × SourceChargeHilbertOutput =>
        (p.1,sourceChargeOutputHilbertEquiv p.2)) :=
    continuous_fst.prodMk
      ((sourceChargeOutputHilbertEquiv).continuous.comp continuous_snd)
  exact hclosed.preimage hcont

/-- Exact domain-density transfer from Gate 65.
This verifies the actual Hilbert adjoint's density hypothesis. -/
theorem sourcePhysicalHilbertChargeColumn_domain_dense :
    Dense ((sourcePhysicalHilbertChargeColumn M G).domain :
      Set G.physicalSpace) := by
  have hs :
      ((sourcePhysicalRebasedChargeColumn M G).domain : Set G.physicalSpace) ⊆
      ((sourcePhysicalHilbertChargeColumn M G).domain : Set G.physicalSpace) := by
    intro ψ hψ
    have hy : ∃ y : SpinIndex → FullL2 2,
        (ψ,y) ∈ sourcePhysicalRebasedChargeGraph M G := by
      have h := (LinearPMap.mem_domain_iff).mp hψ
      rwa [sourcePhysicalRebasedChargeColumn_graph_eq M G] at h
    rcases hy with ⟨y,hy⟩
    apply LinearPMap.mem_domain_of_mem_graph
    rw [sourcePhysicalHilbertChargeColumn_graph_eq M G]
    apply (sourcePhysicalHilbertChargeGraph_mem_iff M G _).mpr
    have hout :
        sourceChargeOutputHilbertEquiv (WithLp.toLp 2 y) = y := by
      rfl
    rw [hout]
    exact hy
  exact (sourcePhysicalRebasedChargeColumn_domain_dense M G).mono hs

/-- Original physical Hilbert subspace remains complete. -/
theorem sourceOriginalPhysicalHilbert_complete :
    CompleteSpace G.physicalSpace :=
  (G.physicalSpace_closed).isComplete.completeSpace_coe

/-- ACTUAL Hilbert adjoint, now over source physical input and
genuine ℓ² sixteen-charge output, with no non-dense fallback. -/
noncomputable def sourceOriginalPhysicalChargeAdjoint :
    SourceChargeHilbertOutput →ₗ.[ℂ] G.physicalSpace := by
  letI : CompleteSpace G.physicalSpace :=
    sourceOriginalPhysicalHilbert_complete M G
  exact (sourcePhysicalHilbertChargeColumn M G).adjoint

theorem sourceOriginalPhysicalChargeAdjoint_isFormalAdjoint :
    (sourceOriginalPhysicalChargeAdjoint M G).IsFormalAdjoint
      (sourcePhysicalHilbertChargeColumn M G) := by
  let : CompleteSpace G.physicalSpace :=
    sourceOriginalPhysicalHilbert_complete M G
  exact LinearPMap.adjoint_isFormalAdjoint
    (sourcePhysicalHilbertChargeColumn_domain_dense M G)

/-- The true physical charge adjoint is a CLOSED unbounded
Hilbert operator; no self-adjoint Hamiltonian is inferred. -/
theorem sourceOriginalPhysicalChargeAdjoint_isClosed :
    (sourceOriginalPhysicalChargeAdjoint M G).IsClosed := by
  let : CompleteSpace G.physicalSpace :=
    sourceOriginalPhysicalHilbert_complete M G
  exact LinearPMap.adjoint_isClosed
    (sourcePhysicalHilbertChargeColumn_domain_dense M G)

/-- Correct physical Hilbert inner product adjoint identity,
where charge outputs carry their ℓ² direct-sum inner product. -/
theorem sourceOriginalPhysicalChargeAdjoint_inner
    (u : (sourcePhysicalHilbertChargeColumn M G).domain)
    (v : (sourceOriginalPhysicalChargeAdjoint M G).domain) :
    inner ℂ (sourceOriginalPhysicalChargeAdjoint M G v)
      (u : G.physicalSpace) =
    inner ℂ (v : SourceChargeHilbertOutput)
      (sourcePhysicalHilbertChargeColumn M G u) := by
  have hformal :
      (sourceOriginalPhysicalChargeAdjoint M G).IsFormalAdjoint
        (sourcePhysicalHilbertChargeColumn M G) :=
    sourceOriginalPhysicalChargeAdjoint_isFormalAdjoint M G
  exact hformal v u

#print axioms sourcePhysicalHilbertChargeGraph_mem_iff
#print axioms sourcePhysicalHilbertChargeColumn_graph_eq
#print axioms sourcePhysicalHilbertChargeColumn_isClosed
#print axioms sourcePhysicalHilbertChargeColumn_domain_dense
#print axioms sourceOriginalPhysicalHilbert_complete
#print axioms sourceOriginalPhysicalChargeAdjoint_isFormalAdjoint
#print axioms sourceOriginalPhysicalChargeAdjoint_isClosed
#print axioms sourceOriginalPhysicalChargeAdjoint_inner

end
end FCP.BFSSSU2PhysicalDomainD2B17
