import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B10CFullHaarCoreCompatibilityAndDensityProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2AClosedPhysicalGraphProbe

/-!
# BFSS SU2 D2B11 — original physical restricted closed charge-column domain

NEW PROSPECTIVE SOURCE-BOUND GATE. No theorem is accepted until
the exact pinned Lean Actions compilation and axiom smoke pass.

This combines the previously qualified:
* exact source-restricted joint-charge graph D1;
* physical inputs/outputs of the restricted graph D2A;
* closed graph vertical uniqueness from pinned OAI ClosedProfiles;
* unconditional source Hilbert-norm physical-core density D2B10C.

The result identifies the genuine original SU2 invariant-core charge
column as a closed, single-valued, densely defined graph over the
source physical Hilbert subspace. The closed graph was already
constructed by the pinned source as a graph closure; the NEW link is
density in the entire true source physical Hilbert space, independently
of any Hamiltonian spectral theorem.

No equality with a MAXIMAL differential-operator realization,
paper self-adjoint Hamiltonian, operator/form graph-norm density
beyond the closure by definition, or spectral prediction is claimed.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B11
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG4K10A
open FCP.BFSSSU2PhysicalDomainD1
open FCP.BFSSSU2PhysicalDomainD2A
open FCP.BFSSSU2PhysicalDomainD2B10C
open MeasureTheory Set

section GenericN
variable {N : ℕ} (M : AlgebraData N) (G : M.GaugeData)

/-- Source gauge-invariant closed charge graph is closed in the
exact ambient full-L2 × sixteen-charge-output Hilbert product. -/
theorem sourceRestrictedPhysicalGraph_isClosed :
    IsClosed (G.deformedModelGraph 1 0 :
      Set (FullL2 N × (SpinIndex → FullL2 N))) := by
  exact (LinearMap.range (G.deformedModelGraphMap 1 0)).isClosed_topologicalClosure

/-- Original source restricted smooth core belongs to the closed
charge graph, with precisely the original source charge column. -/
theorem sourceRestrictedPhysicalGraph_containsCore
    (f : G.invariantCore) :
    (coreToL2 f.val, M.chargeVector f.val) ∈
      G.deformedModelGraph 1 0 := by
  have hp : (coreToL2 f.val, M.deformedChargeVector 1 0 f.val) ∈
      G.deformedModelGraph 1 0 := by
    exact Submodule.le_topologicalClosure _
      (LinearMap.mem_range_self (G.deformedModelGraphMap 1 0) f)
  simpa only [sourceChargeVector_equal M] using hp

/-- A graph point has an original physical input and
all sixteen outputs inside the actual physical Hilbert subspace. -/
theorem sourceRestrictedPhysicalGraph_input_output_physical
    {ψ : FullL2 N} {y : SpinIndex → FullL2 N}
    (hp : (ψ,y) ∈ G.deformedModelGraph 1 0) :
    ψ ∈ G.physicalSpace ∧ ∀ α, y α ∈ G.physicalSpace := by
  exact ⟨sourceClosedGaugeGraph_input_physical M G hp,
    sourceClosedGaugeGraph_output_physical M G hp⟩

/-- The pinned source vertical uniqueness theorem makes this
closed graph genuinely single valued, not a multivalued relation. -/
theorem sourceRestrictedPhysicalGraph_unique
    {ψ : FullL2 N} {y z : SpinIndex → FullL2 N}
    (hy : (ψ,y) ∈ G.deformedModelGraph 1 0)
    (hz : (ψ,z) ∈ G.deformedModelGraph 1 0) :
    y = z := by
  have hvertical : ((0 : FullL2 N),y-z) ∈
      G.deformedModelGraph 1 0 := by
    have hsub := (G.deformedModelGraph 1 0).sub_mem hy hz
    simpa only [Prod.mk_sub_mk, sub_self] using hsub
  exact sub_eq_zero.mp (G.deformedModelGraph_vertical 1 0 hvertical)

end GenericN

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- The new post-Gate-47 physical-domain theorem: the domain
of the exact original closed gauge-restricted joint supercharge
column is HILBERT-NORM DENSE in the ENTIRE source-defined
physical Hilbert space (and contains only physical states).

This asserts density of the operator's DOMAIN in L², not that
the invariant core is graph-norm dense in a MAXIMAL extension.
-/
theorem sourceRestrictedPhysicalGraph_domain_closure_eq_physical :
    closure {ψ : FullL2 2 | ∃ y : SpinIndex → FullL2 2,
      (ψ,y) ∈ G.deformedModelGraph 1 0} =
      (G.physicalSpace : Set (FullL2 2)) := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro ψ ⟨y, hy⟩
      exact sourceClosedGaugeGraph_input_physical M G hy
    · exact G.physicalSpace_closed
  · have hcore :
        (Set.range (coreToL2.comp G.invariantCore.subtype) :
          Set (FullL2 2)) ⊆
        {ψ : FullL2 2 | ∃ y : SpinIndex → FullL2 2,
          (ψ,y) ∈ G.deformedModelGraph 1 0} := by
      rintro ψ ⟨f, rfl⟩
      exact ⟨M.chargeVector f.val,
        sourceRestrictedPhysicalGraph_containsCore M G f⟩
    intro ψ hψ
    have hnorm : ψ ∈ G.coreNormClosure := by
      rw [sourceCoreNormClosure_eq_physical_unconditional M G]
      exact hψ
    have hclosure : ψ ∈
        closure (Set.range (coreToL2.comp G.invariantCore.subtype) :
          Set (FullL2 2)) := by
      exact hnorm
    exact closure_mono hcore hclosure

#print axioms sourceRestrictedPhysicalGraph_isClosed
#print axioms sourceRestrictedPhysicalGraph_containsCore
#print axioms sourceRestrictedPhysicalGraph_input_output_physical
#print axioms sourceRestrictedPhysicalGraph_unique
#print axioms sourceRestrictedPhysicalGraph_domain_closure_eq_physical

end
end FCP.BFSSSU2PhysicalDomainD2B11
