import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B11OriginalPhysicalClosedChargeColumnProbe
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# BFSS SU2 D2B12 — actual Mathlib unbounded closed physical charge operator

PROSPECTIVE until the pinned Lean CI and exact #print axioms gate pass.

Upgrade the exact OAI gauge-restricted closed charge graph from D2B11
into Mathlib's genuine *partially defined linear operator* LinearPMap.
This is NOT a newly invented operator: toLinearPMap is applied to the
ACTUAL source graph G.deformedModelGraph 1 0, and its graph is then
proved equal to that same source graph.

Vertical uniqueness was previously proved by original OAI; D2B11
supplies true source Hilbert-space domain density. A genuine closed,
densely defined linear operator follows by these source proofs,
without assuming a Hamiltonian, normalizability, graph core for a
maximal extension, or spectral theorem.

The output space is still the ambient sixteen-component L²; D2A
separately proves all graph outputs are physical. No false assertion
about an unbounded operator acting on the ENTIRE physical Hilbert
space is introduced.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B12
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2A
open FCP.BFSSSU2PhysicalDomainD2B11
open MeasureTheory Set

section GenericN
variable {N : ℕ} (M : AlgebraData N) (G : M.GaugeData)

/-- The original source restricted graph has zero vertical fiber,
as proved by the pinned source's deformedModelGraph_vertical theorem.
This is the exact prerequisite for extracting a LinearPMap. -/
private theorem sourceRestrictedGraph_vertical_zero :
    ∀ (p : FullL2 N × (SpinIndex → FullL2 N)),
      p ∈ G.deformedModelGraph 1 0 → p.1 = 0 → p.2 = 0 := by
  rintro ⟨ψ,y⟩ hp hzero
  dsimp at hzero
  subst ψ
  exact G.deformedModelGraph_vertical 1 0 hp

/-- Mathlib's actual partially defined ℂ-linear operator formed from
the exact original GaugeData restricted closed charge graph. -/
noncomputable def sourceClosedPhysicalChargeColumn :
    FullL2 N →ₗ.[ℂ] (SpinIndex → FullL2 N) :=
  (G.deformedModelGraph 1 0).toLinearPMap

/-- Exact original source identity of the genuine LinearPMap graph.
No proxy graph or closure is introduced. -/
theorem sourceClosedPhysicalChargeColumn_graph_eq :
    (sourceClosedPhysicalChargeColumn M G).graph =
      G.deformedModelGraph 1 0 := by
  exact Submodule.toLinearPMap_graph_eq _
    (sourceRestrictedGraph_vertical_zero M G)

/-- This is an actual CLOSED UNBOUNDED OPERATOR in Mathlib's sense,
not merely a closed subset with an informal interpretation. -/
theorem sourceClosedPhysicalChargeColumn_isClosed :
    (sourceClosedPhysicalChargeColumn M G).IsClosed := by
  change IsClosed ((sourceClosedPhysicalChargeColumn M G).graph :
    Set (FullL2 N × (SpinIndex → FullL2 N)))
  rw [sourceClosedPhysicalChargeColumn_graph_eq M G]
  exact sourceRestrictedPhysicalGraph_isClosed M G

/-- Every allowed input of the source closed physical supercharge
operator lies in the TRUE source physical Hilbert subspace. -/
theorem sourceClosedPhysicalChargeColumn_domain_le_physical :
    (sourceClosedPhysicalChargeColumn M G).domain ≤ G.physicalSpace := by
  intro ψ hψ
  change ψ ∈ (G.deformedModelGraph 1 0).map
      (LinearMap.fst ℂ (FullL2 N) (SpinIndex → FullL2 N)) at hψ
  obtain ⟨p, hp, heq⟩ := hψ
  subst ψ
  exact sourceClosedGaugeGraph_input_physical M G hp

end GenericN

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- EXACT source physical-space density of the domain of the new
genuine closed LinearPMap at SU2. This is Hilbert-norm density of its
domain, not a maximal-operator graph-core or Hamiltonian statement. -/
theorem sourceClosedPhysicalChargeColumn_domain_closure_eq_physical :
    closure ((sourceClosedPhysicalChargeColumn M G).domain :
        Set (FullL2 2)) =
      (G.physicalSpace : Set (FullL2 2)) := by
  have hdom :
      ((sourceClosedPhysicalChargeColumn M G).domain : Set (FullL2 2)) =
      {ψ : FullL2 2 | ∃ y : SpinIndex → FullL2 2,
        (ψ,y) ∈ G.deformedModelGraph 1 0} := by
    ext ψ
    change ψ ∈ (G.deformedModelGraph 1 0).map
      (LinearMap.fst ℂ (FullL2 2) (SpinIndex → FullL2 2)) ↔
      ∃ y : SpinIndex → FullL2 2,
        (ψ,y) ∈ G.deformedModelGraph 1 0
    simp only [Submodule.mem_map, LinearMap.fst_apply,
      Prod.exists, exists_and_right, exists_eq_right]
  rw [hdom]
  exact sourceRestrictedPhysicalGraph_domain_closure_eq_physical M G

#print axioms sourceClosedPhysicalChargeColumn_graph_eq
#print axioms sourceClosedPhysicalChargeColumn_isClosed
#print axioms sourceClosedPhysicalChargeColumn_domain_le_physical
#print axioms sourceClosedPhysicalChargeColumn_domain_closure_eq_physical

end
end FCP.BFSSSU2PhysicalDomainD2B12
