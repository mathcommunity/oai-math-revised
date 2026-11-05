import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8ATOriginalPiLp16OutputParityUnitaryProbe
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# H5E8AU — literal ORIGINAL source chargeVector minimal closed LinearPMap

This source-pinned construction resolves a *different* math interface
from the inaccessible historical Gate #93 cache. It defines the genuine
partially defined linear operator via the topological closure of the
LITERAL original gauge-invariant smooth core graph:
  (coreToL2 f.val, M.chargeVector f.val).

The pinned ORIGINAL BFSS source Core.lean proves vertical uniqueness
of M.fullClosedGraph for original charges. The original restricted graph
is a subgraph of that exact source full closed graph. Hence its closure
has zero vertical fiber and directly gives a real Mathlib LinearPMap.
No source deformation parameter, 2026 manuscript Hamiltonian, extra
elliptic regularity, maximal differential domain, or new axiom inserted.

This is the original minimal closed chargeVector operator, not yet
the separately qualified D2B12 alias based on deformedModelGraph 1 0.
The equality of those actual SOURCE objects remains a subsequent
bridge requiring source-exact qualified deformed = undeformed identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 240000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AU
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AP
open FCP.BFSSSU2PhysicalDomainL6H5E8AQ

/-- Source original gauge-invariant minimal charge graph, as a true
ℂ-submodule with the actual source SmoothCore chargeVector values. -/
def originalMinimalCoreGraph {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    Submodule ℂ (FullL2 N × (SpinIndex → FullL2 N)) :=
  LinearMap.range
    ((coreToL2.comp G.invariantCore.subtype).prod
      (M.chargeVector.comp G.invariantCore.subtype))

/-- Exact source original graph, with the SOURCE full-L² × sixteen
output topology, not a maximal-operator graph. -/
def originalMinimalClosedGraph {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    Submodule ℂ (FullL2 N × (SpinIndex → FullL2 N)) :=
  (originalMinimalCoreGraph M G).topologicalClosure

/-- This genuinely source-defined closed submodule is EXACTLY the
closed physical core graph set accepted by H5E8AP/H5E8AQ. -/
theorem originalMinimalClosedGraph_set_eq {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    (originalMinimalClosedGraph M G : Set (FullL2 N × (SpinIndex → FullL2 N))) =
      closure (originalPhysicalCoreGraphSet M G) := by
  rfl

/-- Restriction of the ORIGINAL source chargeVector to the genuine
gauge-invariant SmoothCore cannot enlarge its full source graph. -/
theorem originalMinimalClosedGraph_le_full {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    originalMinimalClosedGraph M G ≤ M.fullClosedGraph := by
  change (originalMinimalCoreGraph M G).topologicalClosure ≤
    M.fullCoreGraph.topologicalClosure
  apply Submodule.topologicalClosure_mono
  rintro p ⟨f,rfl⟩
  exact ⟨f.val, rfl⟩

/-- Original-source vertical uniqueness: the genuine minimal
closed physical charge graph has no nonzero vertical fiber.
This is inherited from the ORIGINAL source fullClosedGraph_vertical;
no deformed model or Gate-93 import is used. -/
private theorem originalMinimalClosedGraph_vertical {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    ∀ p : FullL2 N × (SpinIndex → FullL2 N),
      p ∈ originalMinimalClosedGraph M G → p.1 = 0 → p.2 = 0 := by
  rintro ⟨x,y⟩ hp hx
  dsimp at hx
  subst x
  exact M.fullClosedGraph_vertical
    (originalMinimalClosedGraph_le_full M G hp)

/-- TRUE source original minimal closed charge `LinearPMap`,
directly from the exact source `M.chargeVector` graph closure. -/
noncomputable def originalMinimalClosedChargeColumn {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    FullL2 N →ₗ.[ℂ] (SpinIndex → FullL2 N) :=
  (originalMinimalClosedGraph M G).toLinearPMap

/-- Its true Mathlib `LinearPMap.graph` equals the exact gauge-
restricted minimal original BFSS sixteen-charge closed graph. -/
theorem originalMinimalClosedChargeColumn_graph_eq {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    (originalMinimalClosedChargeColumn M G).graph =
      originalMinimalClosedGraph M G := by
  exact Submodule.toLinearPMap_graph_eq _
    (originalMinimalClosedGraph_vertical M G)

/-- Genuine operator graph is closed in the exact original product
space; no general spectral theorem is inferred. -/
theorem originalMinimalClosedChargeColumn_isClosed {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    (originalMinimalClosedChargeColumn M G).IsClosed := by
  change IsClosed ((originalMinimalClosedChargeColumn M G).graph :
    Set (FullL2 N × (SpinIndex → FullL2 N)))
  rw [originalMinimalClosedChargeColumn_graph_eq M G]
  exact (originalMinimalCoreGraph M G).isClosed_topologicalClosure

/-- True `LinearPMap.domain` equals H5E8AQ's exact original
physical closed-graph FIRST-COORDINATE domain. -/
theorem originalMinimalClosedChargeColumn_domain_eq {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    ((originalMinimalClosedChargeColumn M G).domain : Set (FullL2 N)) =
      originalPhysicalClosedChargeDomainSet M G := by
  ext x
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := (LinearPMap.mem_domain_iff).mp hx
    rw [originalMinimalClosedChargeColumn_graph_eq M G] at hy
    exact ⟨y, (congrArg
      (fun S : Set (FullL2 N × (SpinIndex → FullL2 N)) => (x,y) ∈ S)
      (originalMinimalClosedGraph_set_eq M G)).mp hy⟩
  · rintro ⟨y,hy⟩
    apply LinearPMap.mem_domain_of_mem_graph
    rw [originalMinimalClosedChargeColumn_graph_eq M G]
    exact (congrArg
      (fun S : Set (FullL2 N × (SpinIndex → FullL2 N)) => (x,y) ∈ S)
      (originalMinimalClosedGraph_set_eq M G)).mpr hy

#print axioms originalMinimalCoreGraph
#print axioms originalMinimalClosedGraph
#print axioms originalMinimalClosedGraph_set_eq
#print axioms originalMinimalClosedGraph_le_full
#print axioms originalMinimalClosedChargeColumn
#print axioms originalMinimalClosedChargeColumn_graph_eq
#print axioms originalMinimalClosedChargeColumn_isClosed
#print axioms originalMinimalClosedChargeColumn_domain_eq

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AU
