import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H3B2OriginalAYNativePhysicalHilbertChargeColumn

/-!
M4F9 H4B1A — SOURCE-ONLY typed AY physical-output PiLp graph membership
against the original named deformedModelGraph(1,0). This separates the
problematic large AY graph rewrite from the source-independent H4B1
transport proof. No new source operators or changed hypotheses.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H4B1ASourceNamedNativeGraphMembership
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6H5E8AY
open FCP.BFSSSU2PhysicalDomainL6H5E8BF
open FCP.M4F9H3B1OriginalAYNativePhysicalHilbertGraphRebase
open MeasureTheory Set

/-- Actual source AY graph physical-to-physical Hilbert output membership
is precisely membership in the originally named source gauge-restricted
closed 16-charge graph after the canonical input and output embeddings.
This is source-only, not an assumed graph transport through J. -/
theorem pairedNativeSourcePhysicalGraph_mem_source_iff
    (p : pairedGaugeData.physicalSpace ×
      PiLp 2 (fun _ : SpinIndex => pairedGaugeData.physicalSpace)) :
    p ∈ pairedOriginalPhysicalHilbertChargeGraph ↔
      ((p.1 : FullL2 2),
        fun α : SpinIndex => ((p.2 α : pairedGaugeData.physicalSpace) :
          FullL2 2)) ∈ pairedGaugeData.deformedModelGraph 1 0 := by
  rw [pairedOriginalPhysicalHilbertChargeGraph_mem_iff p]
  rw [originalMinimalPhysicalHilbertChargeColumn_graph_eq_sourceRebased
    pairedAlgebraData pairedGaugeData]
  change
    ((p.1 : FullL2 2),
      originalMinimalHilbertOutputEquiv
        (pairedPhysicalHilbertOutputsToOriginalAmbient p.2)) ∈
        pairedGaugeData.deformedModelGraph 1 0 ↔ _
  rfl

#print axioms pairedNativeSourcePhysicalGraph_mem_source_iff
end
end FCP.M4F9H4B1ASourceNamedNativeGraphMembership
