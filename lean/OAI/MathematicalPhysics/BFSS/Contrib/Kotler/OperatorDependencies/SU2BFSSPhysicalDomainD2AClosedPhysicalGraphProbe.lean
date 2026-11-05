import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD3BFullChargeGaugePreservationProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD1RestrictedSourceGraphProbe

/-!
# BFSS Physical Domain D2A — closed joint-charge graph stays physical

PROSPECTIVE / NOT COMPILED until dedicated pinned GitHub Actions gate PASS.
The source physical-space is exactly the BFSS GaugeData.physicalSpace.
The charge-image physical invariance theorem is exactly the Gate-6 D3B
statement, not a new assumption.

D2A proves a closed operator-domain correspondence, NOT density of the
physical smooth core within all source physical L² (future D2B).
-/

namespace FCP.BFSSSU2PhysicalDomainD2A
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG4K9D
open FCP.BFSSSU2PhysicalDomainD1
open FCP.BFSSSU2PhysicalDomainD3B
open MeasureTheory Set

variable {N : ℕ} (M : AlgebraData N) (G : M.GaugeData)

/-- The ordinary L² closure of the gauge-invariant smooth core is
contained in the exact source physical Hilbert subspace, because
physicalSpace is closed. The reverse density inclusion remains OPEN. -/
theorem sourceCoreNormClosure_le_physicalSpace :
    G.coreNormClosure ≤ G.physicalSpace := by
  change (LinearMap.range (coreToL2.comp G.invariantCore.subtype)).topologicalClosure ≤
    G.physicalSpace
  apply Submodule.topologicalClosure_minimal
  · rintro ψ ⟨f, rfl⟩
    exact f.prop
  · exact G.physicalSpace_closed

/-- Every source gauge-restricted closed graph input is an honest
physical state, not merely an arbitrary full-space L² vector. -/
theorem sourceClosedGaugeGraph_input_physical
    {ψ : FullL2 N} {y : SpinIndex → FullL2 N}
    (hp : (ψ, y) ∈ G.deformedModelGraph 1 0) :
    ψ ∈ G.physicalSpace :=
  (sourceCoreNormClosure_le_physicalSpace M G)
    (G.deformedModelGraph_coreNormClosure 1 0 hp)

/-- Every one of the 16 source gauge-restricted closed graph charge
outputs stays in physical L². Closedness is essential: the
smooth-core covariance theorem D3B survives graph-norm limits. -/
theorem sourceClosedGaugeGraph_output_physical
    {ψ : FullL2 N} {y : SpinIndex → FullL2 N}
    (hp : (ψ, y) ∈ G.deformedModelGraph 1 0)
    (α : SpinIndex) :
    y α ∈ G.physicalSpace := by
  let X := FullL2 N × (SpinIndex → FullL2 N)
  have hc : Continuous (fun p : X => p.2 α) :=
    (continuous_apply α).comp continuous_snd
  have hclosed : IsClosed {p : X | p.2 α ∈ G.physicalSpace} :=
    G.physicalSpace_closed.preimage hc
  have hcore :
      (LinearMap.range (G.deformedModelGraphMap 1 0) : Set X) ⊆
        {p : X | p.2 α ∈ G.physicalSpace} := by
    rintro p ⟨f, rfl⟩
    change coreToL2 (M.deformedCoreCharge 1 0 α f.val) ∈ G.physicalSpace
    rw [sourceUnconditionalCoreCharge_equal M α f.val]
    exact sourceOriginalCoreCharge_mem_physicalSpace M G α f
  have hlimit :
      (G.deformedModelGraph 1 0 : Set X) ⊆
        {p : X | p.2 α ∈ G.physicalSpace} := by
    change closure (LinearMap.range (G.deformedModelGraphMap 1 0) : Set X) ⊆ _
    exact closure_minimal hcore hclosed
  exact hlimit hp

/-- Entire original-source physical closed graph, input and all 16
outputs, belongs to the actual source gauge-invariant L² sector.
The "original" graph here is D1's original restricted graph, not
the unrestricted fullClosedGraph. -/
theorem sourceOriginalRestrictedClosedGraph_all_physical
    {ψ : FullL2 N} {y : SpinIndex → FullL2 N}
    (hp : (ψ, y) ∈ originalRestrictedClosedGraph M G) :
    ψ ∈ G.physicalSpace ∧ ∀ α, y α ∈ G.physicalSpace := by
  rw [← sourceGaugeRestrictedClosedGraph_equal M G] at hp
  exact ⟨sourceClosedGaugeGraph_input_physical M G hp,
    sourceClosedGaugeGraph_output_physical M G hp⟩

#print axioms sourceCoreNormClosure_le_physicalSpace
#print axioms sourceClosedGaugeGraph_input_physical
#print axioms sourceClosedGaugeGraph_output_physical
#print axioms sourceOriginalRestrictedClosedGraph_all_physical

end
end FCP.BFSSSU2PhysicalDomainD2A
