import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8BFOriginalSourceGraphAndPairedHamiltonianProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B17TruePhysicalChargeAdjointProbe

/-!
# H5E8BG — exact original AY vs legacy D2B17 source Hilbert charge equality

PROSPECTIVE until strict original pinned kernel and permitted-axiom PASS.

BF qualified the exact gauge restricted closed graph equivalence:
the original AY minimal M.chargeVector invariant SmoothCore closure IS
the original G.deformedModelGraph at (h,m)=(1,0), with no false
equivalence to the ambient unrestricted source fullClosedGraph.

Rebuild historical D2B11–17 in the SAME accepted source environment,
preserving each source SHA, then check ACTUAL equality of the two
separately constructed native Hilbert charge LinearPMaps:
  AY.originalMinimalPhysicalHilbertChargeColumn M G
    = D2B17.sourcePhysicalHilbertChargeColumn M G
(not just equality of pointwise formulas on a test core).

Output equivalence, physical Hilbert graph, operator graph, domain and
paired 48-Majorana/24-boson charge are checked directly, with
D2B16/D2B17 source representations and only the qualified BF graph
identity. No new source assumptions or manuscript equivalences.

Equality of their genuine Hilbert adjoints, their normalized
associated operators and D2B28's concrete historical Hamiltonian
remains a separate source-domain transport target. Neither these nor
paper Spin(48) intertwining, positive eigenvalues or mass gap follow
from the graph crosswalk alone.
-/

set_option autoImplicit false
set_option maxHeartbeats 220000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8BG
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AY
open FCP.BFSSSU2PhysicalDomainL6H5E8BF
open FCP.BFSSSU2PhysicalDomainD2B16
open FCP.BFSSSU2PhysicalDomainD2B17
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4J

/-- The AY and D2B17 sixteen-output complex Hilbert linear
equivalences are literally the same source PiLp-continuous
equivalence, without an invented charge-index or norm change. -/
theorem originalMinimalHilbertOutputEquiv_eq_historical :
    (originalMinimalHilbertOutputEquiv (N := 2)) =
      sourceChargeOutputHilbertEquiv := by
  rfl

/-- The separately defined original AY and D2B17 source graphs
are equal ON THE ENTIRE closed physical Hilbert graph, not only
the original smooth core. -/
theorem originalMinimalPhysicalHilbertChargeGraph_eq_historical
    (M : AlgebraData 2) (G : M.GaugeData) :
    originalMinimalPhysicalHilbertChargeGraph M G =
      sourcePhysicalHilbertChargeGraph M G := by
  ext p
  rw [originalMinimalPhysicalHilbertChargeGraph_mem_source_iff M G p,
      sourcePhysicalHilbertChargeGraph_mem_iff M G p,
      sourcePhysicalRebasedChargeGraph_mem_iff M G _]
  rfl

/-- The genuine native complex-linear unbounded operators agree,
with exactly their full natural source closed domains. -/
theorem originalMinimalPhysicalHilbertChargeColumn_eq_historical
    (M : AlgebraData 2) (G : M.GaugeData) :
    originalMinimalPhysicalHilbertChargeColumn M G =
      sourcePhysicalHilbertChargeColumn M G := by
  apply LinearPMap.eq_of_eq_graph
  rw [originalMinimalPhysicalHilbertChargeColumn_graph_eq M G,
      sourcePhysicalHilbertChargeColumn_graph_eq M G,
      originalMinimalPhysicalHilbertChargeGraph_eq_historical M G]

/-- Domain equality is explicit, not inferred from a comparison of
differential expressions on only invariant test functions. -/
theorem originalMinimalPhysicalHilbertChargeColumn_domain_eq_historical
    (M : AlgebraData 2) (G : M.GaugeData) :
    (originalMinimalPhysicalHilbertChargeColumn M G).domain =
      (sourcePhysicalHilbertChargeColumn M G).domain := by
  rw [originalMinimalPhysicalHilbertChargeColumn_eq_historical M G]

/-- Exact concrete paired SU2 six-field 48-Majorana/24-boson
charge column equals historical source Hilbert charge column. -/
theorem pairedOriginalMinimalChargeColumn_eq_historical :
    originalMinimalPhysicalHilbertChargeColumn
      pairedAlgebraData pairedGaugeData =
    sourcePhysicalHilbertChargeColumn
      pairedAlgebraData pairedGaugeData := by
  exact originalMinimalPhysicalHilbertChargeColumn_eq_historical
    pairedAlgebraData pairedGaugeData

#print axioms originalMinimalHilbertOutputEquiv_eq_historical
#print axioms originalMinimalPhysicalHilbertChargeGraph_eq_historical
#print axioms originalMinimalPhysicalHilbertChargeColumn_eq_historical
#print axioms originalMinimalPhysicalHilbertChargeColumn_domain_eq_historical
#print axioms pairedOriginalMinimalChargeColumn_eq_historical

end
end FCP.BFSSSU2PhysicalDomainL6H5E8BG
