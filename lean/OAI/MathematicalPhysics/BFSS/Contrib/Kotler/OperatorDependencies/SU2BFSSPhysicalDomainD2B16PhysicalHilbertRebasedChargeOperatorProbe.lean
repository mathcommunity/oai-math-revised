import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B15ClosedPhysicalEnergyFormLimitProbe

/-!
# BFSS SU2 D2B16 — exact source operator rebased to the true physical Hilbert space

PROSPECTIVE until pinned Lean 4.34.1 Gate 63+ checks all axioms.

The previously defined closed joint-charge column has a domain dense
ONLY in source G.physicalSpace, not necessarily in ambient unrestricted
FullL2. Mathlib's unbounded adjoint needs domain density in the
operator's genuine ambient Hilbert space. Therefore DO NOT apply
LinearPMap.adjoint to the ambient-FullL2 operator.

This leaf pulls back the EXACT source G.deformedModelGraph 1 0
under the canonical inclusion of G.physicalSpace in FullL2,
uses the source's proved vertical uniqueness, proves the graph
identity and topological closedness, and proves DENSITY within
the precise source physical Hilbert space at N=2.

The output remains 16 components in ambient FullL2; the established
source theorem shows they are all gauge invariant. No paper
Hamiltonian/operator or spectral identification is claimed.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B16
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2A
open FCP.BFSSSU2PhysicalDomainD2B11
open FCP.BFSSSU2PhysicalDomainD2B12
open MeasureTheory Set

section GenericN
variable {N : ℕ} (M : AlgebraData N) (G : M.GaugeData)

/-- The literal source closed restricted graph, pulled back along
canonical source physical-Hilbert inclusion only. -/
noncomputable def sourcePhysicalRebasedChargeGraph :
    Submodule ℂ (G.physicalSpace × (SpinIndex → FullL2 N)) :=
  (G.deformedModelGraph 1 0).comap
    (G.physicalSpace.subtype.prodMap
      (LinearMap.id : (SpinIndex → FullL2 N) →ₗ[ℂ] (SpinIndex → FullL2 N)))

/-- The true graph membership is exactly the original source graph
after embedding physical input in unrestricted FullL2. -/
theorem sourcePhysicalRebasedChargeGraph_mem_iff
    (p : G.physicalSpace × (SpinIndex → FullL2 N)) :
    p ∈ sourcePhysicalRebasedChargeGraph M G ↔
      ((p.1 : FullL2 N), p.2) ∈ G.deformedModelGraph 1 0 := by
  rfl

/-- Original source vertical uniqueness survives pullback with
NO additional gauge or analytic hypotheses. -/
private theorem sourcePhysicalRebasedChargeGraph_vertical :
    ∀ (p : G.physicalSpace × (SpinIndex → FullL2 N)),
      p ∈ sourcePhysicalRebasedChargeGraph M G →
      p.1 = 0 → p.2 = 0 := by
  rintro ⟨ψ,y⟩ hp hz
  have hp' : ((ψ : FullL2 N),y) ∈ G.deformedModelGraph 1 0 :=
    (sourcePhysicalRebasedChargeGraph_mem_iff M G _).mp hp
  have hz' : (ψ : FullL2 N) = 0 :=
    congrArg (fun x : G.physicalSpace => (x : FullL2 N)) hz
  have hzero : ((0 : FullL2 N),y) ∈ G.deformedModelGraph 1 0 := by
    simpa only [hz'] using hp'
  exact G.deformedModelGraph_vertical 1 0 hzero

/-- A genuine Mathlib partially-defined ℂ-linear operator whose
ambient INPUT is the source physical Hilbert subspace itself. -/
noncomputable def sourcePhysicalRebasedChargeColumn :
    G.physicalSpace →ₗ.[ℂ] (SpinIndex → FullL2 N) :=
  (sourcePhysicalRebasedChargeGraph M G).toLinearPMap

/-- The rebased operator graph is exactly the original source graph,
pulled back by the literal physical inclusion. -/
theorem sourcePhysicalRebasedChargeColumn_graph_eq :
    (sourcePhysicalRebasedChargeColumn M G).graph =
      sourcePhysicalRebasedChargeGraph M G := by
  exact Submodule.toLinearPMap_graph_eq _
    (sourcePhysicalRebasedChargeGraph_vertical M G)

/-- Closedness is inherited from the ACTUAL original source graph
by the continuous physical inclusion, not postulated. -/
theorem sourcePhysicalRebasedChargeColumn_isClosed :
    (sourcePhysicalRebasedChargeColumn M G).IsClosed := by
  change IsClosed ((sourcePhysicalRebasedChargeColumn M G).graph :
    Set (G.physicalSpace × (SpinIndex → FullL2 N)))
  rw [sourcePhysicalRebasedChargeColumn_graph_eq M G]
  change IsClosed {p : G.physicalSpace × (SpinIndex → FullL2 N) |
    ((p.1 : FullL2 N),p.2) ∈ G.deformedModelGraph 1 0}
  exact (sourceRestrictedPhysicalGraph_isClosed M G).preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

/-- On the exact rebased graph, every one of sixteen outputs is an
original source physical state. -/
theorem sourcePhysicalRebasedChargeColumn_output_physical
    (u : (sourcePhysicalRebasedChargeColumn M G).domain) (α : SpinIndex) :
    (sourcePhysicalRebasedChargeColumn M G u) α ∈ G.physicalSpace := by
  have hgraph : ((u : G.physicalSpace),
      sourcePhysicalRebasedChargeColumn M G u) ∈
      sourcePhysicalRebasedChargeGraph M G := by
    rw [← sourcePhysicalRebasedChargeColumn_graph_eq M G]
    exact (sourcePhysicalRebasedChargeColumn M G).mem_graph u
  have hp : (((u : G.physicalSpace) : FullL2 N),
      sourcePhysicalRebasedChargeColumn M G u) ∈
      G.deformedModelGraph 1 0 :=
    (sourcePhysicalRebasedChargeGraph_mem_iff M G _).mp hgraph
  exact sourceClosedGaugeGraph_output_physical M G hp α

end GenericN

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- Crucial SU2 source-domain DENSITY, now in the ACTUAL ambient
physical Hilbert space required by Mathlib's unbounded adjoint.
Unlike density in unrestricted FullL2, this follows from Gate 47. -/
theorem sourcePhysicalRebasedChargeColumn_domain_dense :
    Dense ((sourcePhysicalRebasedChargeColumn M G).domain :
      Set G.physicalSpace) := by
  rw [Subtype.dense_iff]
  have hs :
      ((sourceClosedPhysicalChargeColumn M G).domain : Set (FullL2 2)) ⊆
        ((↑) '' ((sourcePhysicalRebasedChargeColumn M G).domain :
          Set G.physicalSpace) : Set (FullL2 2)) := by
    intro ψ hψ
    have hmem : ∃ y : SpinIndex → FullL2 2,
        (ψ,y) ∈ G.deformedModelGraph 1 0 := by
      have h := (LinearPMap.mem_domain_iff).mp hψ
      rwa [sourceClosedPhysicalChargeColumn_graph_eq M G] at h
    rcases hmem with ⟨y,hy⟩
    let v : G.physicalSpace :=
      ⟨ψ,sourceClosedGaugeGraph_input_physical M G hy⟩
    refine ⟨v, ?_, rfl⟩
    apply LinearPMap.mem_domain_of_mem_graph
    rw [sourcePhysicalRebasedChargeColumn_graph_eq M G]
    exact (sourcePhysicalRebasedChargeGraph_mem_iff M G _).mpr hy
  calc
    (G.physicalSpace : Set (FullL2 2)) =
        closure ((sourceClosedPhysicalChargeColumn M G).domain :
          Set (FullL2 2)) :=
      (sourceClosedPhysicalChargeColumn_domain_closure_eq_physical M G).symm
    _ ≤ closure ((↑) '' ((sourcePhysicalRebasedChargeColumn M G).domain :
          Set G.physicalSpace) : Set (FullL2 2)) :=
      closure_mono hs

#print axioms sourcePhysicalRebasedChargeGraph_mem_iff
#print axioms sourcePhysicalRebasedChargeColumn_graph_eq
#print axioms sourcePhysicalRebasedChargeColumn_isClosed
#print axioms sourcePhysicalRebasedChargeColumn_output_physical
#print axioms sourcePhysicalRebasedChargeColumn_domain_dense

end
end FCP.BFSSSU2PhysicalDomainD2B16
