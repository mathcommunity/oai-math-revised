import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AUOriginalMinimalClosedChargeLinearPMapProbe

/-!
# H5E8AV — source original minimal CLOSED charge operator action parity

PROSPECTIVE: strict source-pinned Lean, no theorem accepted until gated.
Uses AU's literal ORIGINAL source M.chargeVector graph closure and
actual unbounded `LinearPMap`, plus AQ's qualified graph/domain parity
and the pinned source Core.lean full closed graph uniqueness.

This is a real operator action equivalence ON ITS NATURAL DOMAIN,
not merely a smooth-core identity. The target is oppositeGamma M with
the exact source-reconstructed gauge datum; all 16 outputs undergo
true original spatial parity. No proxy Hamiltonian, deformed-model
identification, maximal operator extension, or paper spectral claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 250000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AV
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AD
open FCP.BFSSSU2PhysicalDomainL6H5E8AI
open FCP.BFSSSU2PhysicalDomainL6H5E8AN
open FCP.BFSSSU2PhysicalDomainL6H5E8AP
open FCP.BFSSSU2PhysicalDomainL6H5E8AQ
open FCP.BFSSSU2PhysicalDomainL6H5E8AS
open FCP.BFSSSU2PhysicalDomainL6H5E8AU

/-- Exact graph membership equivalence for the TRUE original minimal
closed charge operator, separately instantiated at the opposite gamma
source with its actual physical GaugeData. -/
theorem originalMinimalChargeOperator_graph_mem_iff {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    (x : FullL2 N) (y : SpinIndex → FullL2 N) :
    (x,y) ∈ (originalMinimalClosedChargeColumn M G).graph ↔
      (originalFullL2Parity x,
        fun α => originalFullL2Parity (y α)) ∈
      (originalMinimalClosedChargeColumn (oppositeGamma M)
        (originalOppositeGammaGaugeData M G)).graph := by
  rw [originalMinimalClosedChargeColumn_graph_eq M G,
      originalMinimalClosedChargeColumn_graph_eq
        (oppositeGamma M) (originalOppositeGammaGaugeData M G)]
  change ((x,y) ∈ (originalMinimalClosedGraph M G :
      Set (FullL2 N × (SpinIndex → FullL2 N)))) ↔
    ((originalFullL2Parity x, fun α => originalFullL2Parity (y α)) ∈
      (originalMinimalClosedGraph (oppositeGamma M)
        (originalOppositeGammaGaugeData M G) :
        Set (FullL2 N × (SpinIndex → FullL2 N))))
  rw [originalMinimalClosedGraph_set_eq M G,
      originalMinimalClosedGraph_set_eq
        (oppositeGamma M) (originalOppositeGammaGaugeData M G)]
  exact originalPhysicalClosedGraph_mem_iff M G x y

/-- True Mathlib `LinearPMap.domain` parity; no auxiliary or maximal
operator domain is inferred. -/
theorem originalMinimalChargeOperator_domain_mem_iff {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    (x : FullL2 N) :
    x ∈ (originalMinimalClosedChargeColumn M G).domain ↔
      originalFullL2Parity x ∈
      (originalMinimalClosedChargeColumn (oppositeGamma M)
        (originalOppositeGammaGaugeData M G)).domain := by
  change (x ∈ ((originalMinimalClosedChargeColumn M G).domain :
        Set (FullL2 N))) ↔
    (originalFullL2Parity x ∈
      ((originalMinimalClosedChargeColumn (oppositeGamma M)
        (originalOppositeGammaGaugeData M G)).domain : Set (FullL2 N)))
  rw [originalMinimalClosedChargeColumn_domain_eq M G,
      originalMinimalClosedChargeColumn_domain_eq
        (oppositeGamma M) (originalOppositeGammaGaugeData M G)]
  exact originalPhysicalClosedChargeDomain_mem_iff M G x

/-- Canonical actual-domain map induced by parity. It is built from
the proved native operator-domain iff, not an assumed domain equality. -/
noncomputable def originalMinimalChargeDomainParityMap {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    (u : (originalMinimalClosedChargeColumn M G).domain) :
    (originalMinimalClosedChargeColumn (oppositeGamma M)
      (originalOppositeGammaGaugeData M G)).domain :=
  ⟨originalFullL2Parity (u : FullL2 N),
    (originalMinimalChargeOperator_domain_mem_iff M G
      (u : FullL2 N)).mp u.property⟩

/-- Exact operator-valued action parity of all 16 charges ON THE
ACTUAL MINIMAL CLOSED SOURCE DOMAIN. This follows from the two
graph points and original source fullClosedGraph_unique, not a
differential expression compared only on Schwartz test functions. -/
theorem originalMinimalChargeOperator_action_parity {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    (u : (originalMinimalClosedChargeColumn M G).domain) :
    originalMinimalClosedChargeColumn
        (oppositeGamma M) (originalOppositeGammaGaugeData M G)
        (originalMinimalChargeDomainParityMap M G u) =
      fun α => originalFullL2Parity
        ((originalMinimalClosedChargeColumn M G u) α) := by
  have hp : ((originalFullL2Parity (u : FullL2 N)),
      fun α => originalFullL2Parity
        ((originalMinimalClosedChargeColumn M G u) α)) ∈
      (originalMinimalClosedChargeColumn (oppositeGamma M)
        (originalOppositeGammaGaugeData M G)).graph :=
    (originalMinimalChargeOperator_graph_mem_iff M G
      (u : FullL2 N) (originalMinimalClosedChargeColumn M G u)).mp
      ((originalMinimalClosedChargeColumn M G).mem_graph u)
  have ht : ((originalFullL2Parity (u : FullL2 N)),
      originalMinimalClosedChargeColumn
        (oppositeGamma M) (originalOppositeGammaGaugeData M G)
        (originalMinimalChargeDomainParityMap M G u)) ∈
      (originalMinimalClosedChargeColumn (oppositeGamma M)
        (originalOppositeGammaGaugeData M G)).graph := by
    exact (originalMinimalClosedChargeColumn (oppositeGamma M)
      (originalOppositeGammaGaugeData M G)).mem_graph
        (originalMinimalChargeDomainParityMap M G u)
  rw [originalMinimalClosedChargeColumn_graph_eq] at hp ht
  exact (oppositeGamma M).fullClosedGraph_unique
    (originalMinimalClosedGraph_le_full (oppositeGamma M)
      (originalOppositeGammaGaugeData M G) ht)
    (originalMinimalClosedGraph_le_full (oppositeGamma M)
      (originalOppositeGammaGaugeData M G) hp)

/-- Actual source original closed operator action preserves its exact
1/16 sixteen-charge energy when both sides are evaluated on their
correct natural domains. This is not yet Hamiltonian-domain parity. -/
theorem originalMinimalChargeOperator_energy_parity {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    (u : (originalMinimalClosedChargeColumn M G).domain) :
    originalChargeOutputEnergy
      (originalMinimalClosedChargeColumn
        (oppositeGamma M) (originalOppositeGammaGaugeData M G)
        (originalMinimalChargeDomainParityMap M G u)) =
    originalChargeOutputEnergy (originalMinimalClosedChargeColumn M G u) := by
  rw [originalMinimalChargeOperator_action_parity M G u]
  exact originalChargeOutputEnergy_parity
    (originalMinimalClosedChargeColumn M G u)

#print axioms originalMinimalChargeOperator_graph_mem_iff
#print axioms originalMinimalChargeOperator_domain_mem_iff
#print axioms originalMinimalChargeDomainParityMap
#print axioms originalMinimalChargeOperator_action_parity
#print axioms originalMinimalChargeOperator_energy_parity

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AV
