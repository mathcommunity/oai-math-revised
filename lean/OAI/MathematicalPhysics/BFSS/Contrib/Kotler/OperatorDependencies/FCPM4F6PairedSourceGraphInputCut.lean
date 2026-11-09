import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPRestrictedGraphInputCut

/-!
M4F6 C1 — exact original source gauge-restricted smooth-core graph input cut.

A single source-only specialization of the generic original graph-input
restriction theorem to the literal pairedAlgebraData and pairedGaugeData.
No independent gauge transport, graph image correspondence or closure
statement is imported into the *candidate proof*.

This theorem is a proof-interface certificate, not operator closability,
physical output invariance, physical Hamiltonian equivalence or spectrum.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.M4F6PairedSourceGraphInputCut
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.RestrictedGraphInputCut

/-- Genuine original SU(2) gauge-restricted 16-charge core graph equals
the literal original full-core graph intersected with the true physical
input constraint, before any graph transport or closure. -/
theorem pairedSourceCoreGraph_eq_physicalInputCut :
    (LinearMap.range
      ((coreToL2.comp pairedGaugeData.invariantCore.subtype).prod
        (pairedAlgebraData.chargeVector.comp
          pairedGaugeData.invariantCore.subtype)) :
      Set (FullL2 2 × (SpinIndex → FullL2 2))) =
    {p | p ∈ pairedAlgebraData.fullCoreGraph ∧
      p.1 ∈ pairedGaugeData.physicalSpace} := by
  exact original_core_graph_input_cut
    (M := pairedAlgebraData) (G := pairedGaugeData)

#print axioms pairedSourceCoreGraph_eq_physicalInputCut
#check pairedSourceCoreGraph_eq_physicalInputCut

end
end FCP.M4F6PairedSourceGraphInputCut
