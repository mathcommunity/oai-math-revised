import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H2ActualOriginalSmoothGaugeIntegrableEnvelopeProbe

/-!
L6H2T — source SU(2) is first-countable because it is the
ACTUAL matrix special-unitary subgroup, hence the subtype of
finite 2×2 complex matrices with their pointwise topology.
No new topology, no hypothesis, no mathematical surrogate.

Isolation note: #238 Lean failed to synthesize this instance at
continuous_of_dominated; #239 runner stopped during a monolithic
attempt to elaborate a local instance inside the huge L6H3 proof.
Qualify this native topology lemma SEPARATELY before the analytic
theorem to prevent endless elaboration without compiler feedback.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.BFSSSU2PhysicalDomainL6H2T
noncomputable section
open OAI.BFSSQuantum

/-- First-countability of the ORIGINAL pinned GaugeGroup 2,
derived from the actual matrix function topology and Subtype. -/
theorem actualOriginalSU2_firstCountable :
    FirstCountableTopology (GaugeGroup 2) := by
  have hPi : FirstCountableTopology (Fin 2 → Fin 2 → ℂ) := by
    infer_instance
  have hMat : FirstCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := by
    exact hPi
  letI : FirstCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := hMat
  change FirstCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ)
  -- Mathlib/Topology/Bases.lean: this *instance* lives under
  -- TopologicalSpace.Subtype, not at root Subtype.
  exact TopologicalSpace.Subtype.firstCountableTopology _

#print axioms actualOriginalSU2_firstCountable
#check @actualOriginalSU2_firstCountable

end
end FCP.BFSSSU2PhysicalDomainL6H2T
