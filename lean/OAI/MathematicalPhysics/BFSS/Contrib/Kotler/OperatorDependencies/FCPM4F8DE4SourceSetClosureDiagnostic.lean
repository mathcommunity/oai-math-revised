import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7PhysicalGraphTransportE4
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD1RestrictedSourceGraphProbe

/-!
BFSS M4F8 DE4 diagnostic — isolate the exact original source
Submodule/set-closure bridge independently of the full DE3 transport.

Both assertions are about literal original pinned BFSS objects, not
new charge dynamics. The second has EXACTLY the left-hand Set type of
the already-qualified DE3 closure transport theorem.

A green of this file alone does NOT accept the DE4 physical graph
correspondence. It only localizes the model-independent closure
elaboration/definitional-equality boundary.

Original D1, E4 and all imported mathematical sources unchanged.
-/
set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F8DE4SourceSetClosureDiagnostic
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open MeasureTheory Set

/-- Original D1 gauge-invariant 17-slot closed submodule has exactly
the standard topological closure carrier, as a literal source Set. -/
theorem originalRestrictedClosedGraph_coe_eq_explicitClosure :
    (FCP.BFSSSU2PhysicalDomainD1.originalRestrictedClosedGraph
       pairedAlgebraData pairedGaugeData :
         Set (FullL2 2 × (SpinIndex → FullL2 2))) =
    closure (LinearMap.range
      ((coreToL2.comp pairedGaugeData.invariantCore.subtype).prod
        (pairedAlgebraData.chargeVector.comp
          pairedGaugeData.invariantCore.subtype)) :
        Set (FullL2 2 × (SpinIndex → FullL2 2))) := by
  simp only [FCP.BFSSSU2PhysicalDomainD1.originalRestrictedClosedGraph,
    Submodule.topologicalClosure_coe]

/-- This is only the ORIGINAL named source deformedModelGraph closure,
with no independently constructed operator or transport on either side. -/
theorem pairedSourceNamedGraph_eq_explicitRestrictedClosure :
    (pairedGaugeData.deformedModelGraph 1 0 :
      Set (FullL2 2 × (SpinIndex → FullL2 2))) =
    closure (LinearMap.range
      ((coreToL2.comp pairedGaugeData.invariantCore.subtype).prod
        (pairedAlgebraData.chargeVector.comp
          pairedGaugeData.invariantCore.subtype)) :
        Set (FullL2 2 × (SpinIndex → FullL2 2))) := by
  calc
    (pairedGaugeData.deformedModelGraph 1 0 :
        Set (FullL2 2 × (SpinIndex → FullL2 2))) =
      (FCP.BFSSSU2PhysicalDomainD1.originalRestrictedClosedGraph
        pairedAlgebraData pairedGaugeData :
          Set (FullL2 2 × (SpinIndex → FullL2 2))) :=
      congrArg
        (fun S : Submodule ℂ (FullL2 2 × (SpinIndex → FullL2 2)) =>
          (S : Set (FullL2 2 × (SpinIndex → FullL2 2))))
        (FCP.BFSSSU2PhysicalDomainD1.sourceGaugeRestrictedClosedGraph_equal
          pairedAlgebraData pairedGaugeData)
    _ = _ := originalRestrictedClosedGraph_coe_eq_explicitClosure

#print axioms originalRestrictedClosedGraph_coe_eq_explicitClosure
#print axioms pairedSourceNamedGraph_eq_explicitRestrictedClosure

end
end FCP.M4F8DE4SourceSetClosureDiagnostic
