import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4E1AOriginalAmbientOutputInnerBridge

/-!
BFSS M4F9 H4E1B — exact original AY ambient-output action of the
separately source-defined native physical-output charge.

This is a SOURCE-ONLY consequence of the H3B1 graph preimage and
H3B2 native LinearPMap graph equality. It does NOT need arbitrary
independent Clifford or representation-matching witnesses.

The original AY charge is unchanged. Its ambient FullL2 output is
the ACTUAL physical-output charge embedded by the literal H3B1
inclusion, on the genuine native natural domain.

Do not infer ambient surjectivity, equality of reverse domains,
Hilbert adjoints, Hamiltonians, or spectra from this module.
-/
set_option autoImplicit false
set_option maxHeartbeats 180000

namespace FCP.M4F9H4E1BOriginalAYAmbientChargeAction
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6H5E8AY
open FCP.M4F9H3B1OriginalAYNativePhysicalHilbertGraphRebase
open FCP.M4F9H3B2OriginalAYNativePhysicalHilbertChargeColumn
open MeasureTheory Set

/-- The actual native AY source charge graph embeds into the ACTUAL
original ambient-output AY graph, by the defining source graph
preimage alone. No representation or matching hypotheses. -/
theorem pairedOriginalAmbientCharge_graph_ofNative
    (u : pairedGaugeData.physicalSpace)
    (hu : u ∈ pairedOriginalNativePhysicalHilbertChargeColumn.domain) :
    (u, pairedPhysicalHilbertOutputsToOriginalAmbient
      (pairedOriginalNativePhysicalHilbertChargeColumn ⟨u,hu⟩)) ∈
      (originalMinimalPhysicalHilbertChargeColumn
        pairedAlgebraData pairedGaugeData).graph := by
  have hn :
      (u, pairedOriginalNativePhysicalHilbertChargeColumn ⟨u,hu⟩) ∈
        pairedOriginalNativePhysicalHilbertChargeColumn.graph :=
    pairedOriginalNativePhysicalHilbertChargeColumn.mem_graph ⟨u,hu⟩
  rw [pairedOriginalNativePhysicalHilbertChargeColumn_graph_eq] at hn
  exact (pairedOriginalPhysicalHilbertChargeGraph_mem_iff _).mp hn

/-- Any vector in the source-native natural charge domain is in the
actual AY ambient-output charge domain; the reverse is a distinct
source-output-physicality obligation qualified in H3B2. -/
theorem pairedOriginalAmbientCharge_domain_ofNative
    (u : pairedGaugeData.physicalSpace)
    (hu : u ∈ pairedOriginalNativePhysicalHilbertChargeColumn.domain) :
    u ∈ (originalMinimalPhysicalHilbertChargeColumn
      pairedAlgebraData pairedGaugeData).domain := by
  apply LinearPMap.mem_domain_of_mem_graph
  exact pairedOriginalAmbientCharge_graph_ofNative u hu

/-- Exact AY AMBIENT charge action is inclusion of the ORIGINAL
native Hilbert charge action, on every genuine native domain vector.
No adjoint or H=(1/16)T†T equality is asserted yet. -/
theorem pairedOriginalAmbientCharge_action_ofNative
    (u : pairedGaugeData.physicalSpace)
    (hu : u ∈ pairedOriginalNativePhysicalHilbertChargeColumn.domain) :
    (originalMinimalPhysicalHilbertChargeColumn
      pairedAlgebraData pairedGaugeData)
        ⟨u, pairedOriginalAmbientCharge_domain_ofNative u hu⟩ =
      pairedPhysicalHilbertOutputsToOriginalAmbient
        (pairedOriginalNativePhysicalHilbertChargeColumn ⟨u,hu⟩) := by
  let T := originalMinimalPhysicalHilbertChargeColumn
    pairedAlgebraData pairedGaugeData
  have ht :
      (u, T ⟨u, pairedOriginalAmbientCharge_domain_ofNative u hu⟩) ∈
        T.graph :=
    T.mem_graph ⟨u, pairedOriginalAmbientCharge_domain_ofNative u hu⟩
  have hs :
      (u, pairedPhysicalHilbertOutputsToOriginalAmbient
        (pairedOriginalNativePhysicalHilbertChargeColumn ⟨u,hu⟩)) ∈
        T.graph :=
    pairedOriginalAmbientCharge_graph_ofNative u hu
  exact T.mem_graph_snd_inj ht hs rfl

#print axioms pairedOriginalAmbientCharge_graph_ofNative
#print axioms pairedOriginalAmbientCharge_domain_ofNative
#print axioms pairedOriginalAmbientCharge_action_ofNative
end
end FCP.M4F9H4E1BOriginalAYAmbientChargeAction
