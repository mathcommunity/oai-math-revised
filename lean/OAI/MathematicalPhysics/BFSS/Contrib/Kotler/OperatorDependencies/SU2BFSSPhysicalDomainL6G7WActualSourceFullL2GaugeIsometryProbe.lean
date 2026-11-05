import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7VActualSourceFullL2PhysicalFixedSpaceProbe

/-!
L6G7W — sharpen exact ORIGINAL BFSS FullL2 SU(2) gauge pair
from the verified uniform contraction in L6G7U to EXACT ISOMETRY.

The source fermionic fiberAction norm <= is L6G7U. The true
source inverse cancellation is L6G7V (#225). Applying both to
g and g⁻¹ forces norm preservation. The original bosonPullback
is already a source-exact L2 isometry; its composition with the
fermion fiber action therefore preserves the full BFSS L2 norm.

This does NOT claim the new FullL2 combined action's group law,
its strong SU2 parameter continuity, its strong derivative or
a closed unbounded Gauss generator. No new hypotheses or
surrogate Hilbert spaces; no BFSS spectral conclusions.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace FCP.BFSSSU2PhysicalDomainL6G7W
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6G7V

/-- Exact original Fock-unitary source action is norm-preserving
after its pinned pointwise finite-group inverse is transported
to the genuine FullL2 space. -/
theorem originalSourceFermionFiberAction_norm
    (g : GaugeGroup 2) (v : FullL2 2) :
    ‖pairedGaugeData.fiberAction g v‖ = ‖v‖ := by
  apply le_antisymm
  · exact originalSourceFermionFiberAction_norm_le g v
  · have hcancel :
        pairedGaugeData.fiberAction g⁻¹
          (pairedGaugeData.fiberAction g v) = v := by
      simpa only [inv_inv] using
        (actualSourceFermionFiberAction_inv_cancel g⁻¹ v)
    calc
      ‖v‖ = ‖pairedGaugeData.fiberAction g⁻¹
        (pairedGaugeData.fiberAction g v)‖ := by rw [hcancel]
      _ ≤ ‖pairedGaugeData.fiberAction g v‖ :=
        originalSourceFermionFiberAction_norm_le g⁻¹ _

/-- Every ORIGINAL combined SU2 gauge map is norm preserving on
the entire actual BFSS FullL2 Hilbert space, strengthening U (#223). -/
theorem actualOriginalFullL2GaugePair_norm
    (g : GaugeGroup 2) (v : FullL2 2) :
    ‖actualOriginalFullL2GaugePairCLM g v‖ = ‖v‖ := by
  rw [actualOriginalFullL2GaugePairCLM_apply,
    originalSourceFermionFiberAction_norm,
    originalSourceBosonPullback_norm]

/-- Same source-exact map is an isometry of the actual FullL2 metric.
Surjectivity and an SU2 group homomorphism remain separate steps. -/
theorem actualOriginalFullL2GaugePair_isometry
    (g : GaugeGroup 2) :
    Isometry (actualOriginalFullL2GaugePairCLM g :
      FullL2 2 → FullL2 2) := by
  -- #226: Isometry is defined via edist, not ordinary real norm/dist.
  -- Use Mathlib's native additive-map norm-preservation → isometry.
  exact AddMonoidHomClass.isometry_of_norm
    (actualOriginalFullL2GaugePairCLM g)
    (actualOriginalFullL2GaugePair_norm g)

#print axioms originalSourceFermionFiberAction_norm
#print axioms actualOriginalFullL2GaugePair_norm
#print axioms actualOriginalFullL2GaugePair_isometry
#check @actualOriginalFullL2GaugePair_isometry

end
end FCP.BFSSSU2PhysicalDomainL6G7W
