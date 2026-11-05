import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD3BFullChargeGaugePreservationProbe

/-!
M4F1 S1 — isolated *original-source* specialization certificate.

This file intentionally imports no independent charge or transport modules.
It attempts to specialize the already strict-qualified, generic original
D3B gauge-invariant core preservation theorem to literal paired SU(2)
AlgebraData and GaugeData; it does NOT establish M4F1 by itself.

If elaboration recurses, the obstruction lies at specialization of the
source theorem, not at the independent input/output transport proof.
Do not change the original BFSS source or increase recursion depth.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.BFSSM4F1SourceSpecialization
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainD3B

/-- Exact original paired BFSS charge preservation for every actual
paired source-invariant smooth-core section. No independent transport. -/
theorem pairedOriginalCharge_mem_invariantCore
    (α : SpinIndex) (g : pairedGaugeData.invariantCore) :
    pairedAlgebraData.charge α g.val ∈ pairedGaugeData.invariantCore := by
  exact sourceOriginalCoreCharge_mem_invariantCore
    (M := pairedAlgebraData) (G := pairedGaugeData) α g

#print axioms pairedOriginalCharge_mem_invariantCore
#check pairedOriginalCharge_mem_invariantCore

end
end FCP.BFSSM4F1SourceSpecialization
