import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B12OriginalPhysicalChargeLinearPMapProbe

/-!
# BFSS SU2 D2B13 — source invariant smooth-core column closes to exact physical column

PROSPECTIVE until pinned compiler and exact permitted-axiom smoke PASS.

This uses Mathlib's actual theory of closed and closable partially-defined
linear operators. The source invariant SmoothCore charge column is a
LinearPMap made from the ORIGINAL SOURCE raw restricted graph,
not a replacement domain. Its operator closure is then identified
with the D2B12 closed densely-defined charge operator.

This justifies "smooth invariant core is a graph-norm core" ONLY for
this specific source MINIMAL CLOSED COLUMN by its definition. It does
NOT prove the minimal graph equals an arbitrary MAXIMAL differential
realization, nor any Hamiltonian essential self-adjointness, bound
states or spectral properties.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B13
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD1
open FCP.BFSSSU2PhysicalDomainD2B12
open MeasureTheory Set

variable {N : ℕ} (M : AlgebraData N) (G : M.GaugeData)

/-- The literal source restricted invariant-core charge graph,
prior to its closure in the original L² × 16 L² product space. -/
private def sourceOriginalRestrictedCoreChargeGraph :
    Submodule ℂ (FullL2 N × (SpinIndex → FullL2 N)) :=
  LinearMap.range (G.deformedModelGraphMap 1 0)

/-- Vertical uniqueness holds on the raw source restricted graph,
by inclusion in the pinned source closed graph and its genuine
source theorem deformedModelGraph_vertical. -/
private theorem sourceOriginalRestrictedCoreGraph_vertical_zero :
    ∀ (p : FullL2 N × (SpinIndex → FullL2 N)),
      p ∈ sourceOriginalRestrictedCoreChargeGraph M G →
      p.1 = 0 → p.2 = 0 := by
  rintro ⟨ψ,y⟩ hp hzero
  have hp' : (ψ,y) ∈ G.deformedModelGraph 1 0 :=
    Submodule.le_topologicalClosure _ hp
  dsimp at hzero
  subst ψ
  exact G.deformedModelGraph_vertical 1 0 hp'

/-- Genuine Mathlib partially-defined core supercharge column.
Its graph is the original source gauge-invariant SmoothCore graph,
NOT a fabricated auxiliary graph. -/
noncomputable def sourceOriginalCoreChargePMap :
    FullL2 N →ₗ.[ℂ] (SpinIndex → FullL2 N) :=
  (sourceOriginalRestrictedCoreChargeGraph M G).toLinearPMap

/-- Exact graph identity for the unclosed source core operator. -/
theorem sourceOriginalCoreChargePMap_graph_eq :
    (sourceOriginalCoreChargePMap M G).graph =
      sourceOriginalRestrictedCoreChargeGraph M G := by
  exact Submodule.toLinearPMap_graph_eq _
    (sourceOriginalRestrictedCoreGraph_vertical_zero M G)

/-- The domain of the actual core operator is precisely the image of
the ORIGINAL source invariant SmoothCore under ORIGINAL coreToL2. -/
theorem sourceOriginalCoreChargePMap_domain_eq_embedded :
    (sourceOriginalCoreChargePMap M G).domain =
      LinearMap.range (coreToL2.comp G.invariantCore.subtype) := by
  change (LinearMap.range (G.deformedModelGraphMap 1 0)).map
      (LinearMap.fst ℂ (FullL2 N) (SpinIndex → FullL2 N)) =
    LinearMap.range (coreToL2.comp G.invariantCore.subtype)
  rw [← LinearMap.range_comp]
  congr 1

/-- Source core operator is closable: its graph closure is precisely
the previously established closed source charge column graph. -/
theorem sourceOriginalCoreChargePMap_isClosable :
    (sourceOriginalCoreChargePMap M G).IsClosable := by
  refine ⟨sourceClosedPhysicalChargeColumn M G, ?_⟩
  rw [sourceOriginalCoreChargePMap_graph_eq M G,
      sourceClosedPhysicalChargeColumn_graph_eq M G]
  rfl

/-- The closure of the original gauge-invariant smooth-core charge
operator is EXACTLY the source-defined closed physical operator. -/
theorem sourceOriginalCoreChargePMap_closure_eq_closed :
    (sourceOriginalCoreChargePMap M G).closure =
      sourceClosedPhysicalChargeColumn M G := by
  apply LinearPMap.eq_of_eq_graph
  calc
    (sourceOriginalCoreChargePMap M G).closure.graph =
        (sourceOriginalCoreChargePMap M G).graph.topologicalClosure := by
          exact (sourceOriginalCoreChargePMap_isClosable M G).graph_closure_eq_closure_graph.symm
    _ = (sourceClosedPhysicalChargeColumn M G).graph := by
          rw [sourceOriginalCoreChargePMap_graph_eq M G,
              sourceClosedPhysicalChargeColumn_graph_eq M G]
          rfl

/-- Mathlib's native graph-core statement, for the original core
operator and the particular MINIMAL closed operator it generates. -/
theorem sourceOriginalCoreChargePMap_hasCore :
    (sourceClosedPhysicalChargeColumn M G).HasCore
      (sourceOriginalCoreChargePMap M G).domain := by
  rw [← sourceOriginalCoreChargePMap_closure_eq_closed M G]
  exact (sourceOriginalCoreChargePMap M G).closureHasCore

/-- Source-bound final result: the ORIGINAL embedded gauge-invariant
smooth-core domain is a Mathlib graph-norm core of the actual source
minimal closed charge column. This makes NO claim about a larger
maximal realization or Hamiltonian self-adjointness. -/
theorem sourceInvariantSmoothCore_isGraphCoreOfMinimalClosedColumn :
    (sourceClosedPhysicalChargeColumn M G).HasCore
      (LinearMap.range (coreToL2.comp G.invariantCore.subtype)) := by
  rw [← sourceOriginalCoreChargePMap_domain_eq_embedded M G]
  exact sourceOriginalCoreChargePMap_hasCore M G

#print axioms sourceOriginalCoreChargePMap_graph_eq
#print axioms sourceOriginalCoreChargePMap_domain_eq_embedded
#print axioms sourceOriginalCoreChargePMap_isClosable
#print axioms sourceOriginalCoreChargePMap_closure_eq_closed
#print axioms sourceOriginalCoreChargePMap_hasCore
#print axioms sourceInvariantSmoothCore_isGraphCoreOfMinimalClosedColumn

end
end FCP.BFSSSU2PhysicalDomainD2B13
