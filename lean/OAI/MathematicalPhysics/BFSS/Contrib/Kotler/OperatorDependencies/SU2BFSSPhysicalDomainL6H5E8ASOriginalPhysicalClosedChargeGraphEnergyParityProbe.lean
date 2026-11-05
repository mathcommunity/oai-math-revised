import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AQOriginalPhysicalClosedChargeDomainParityProbe

/-!
# H5E8AS — original physical closed sixteen-charge graph ENERGY parity

Targeted after H5E8AR's inaccessible historical Gate-93 object cache.
Stay strictly within AQ's ACCEPTED actual original restricted source
chargeVector graph closure and the accepted exact original FullL2 parity
isometry. This proves pointwise preservation of the exact source scalar
factor 1/16 times the squared norm of all sixteen charge outputs,
both on general graph outputs and the TRUE gauge-restricted closed graph.

Not a new arbitrary charge or Hamiltonian; output-energy expression
matches the exact source M.coreForm convention on the original core.
No transfer of paper Cl(48) realization, closed Hilbert form/operator
domains, Spin(9) spectrum, or maximal differential operator claimed.
-/

set_option autoImplicit false
set_option maxHeartbeats 220000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AS
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AD
open FCP.BFSSSU2PhysicalDomainL6H5E8AI
open FCP.BFSSSU2PhysicalDomainL6H5E8AN
open FCP.BFSSSU2PhysicalDomainL6H5E8AP
open FCP.BFSSSU2PhysicalDomainL6H5E8AQ

/-- Genuine source FullL2 parity preserves norm on arbitrary
original boson/fermion L2 states. No pointwise L2 representative
or unqualified Fock norm equivalence is used. -/
theorem originalFullL2Parity_norm {N : ℕ} (x : FullL2 N) :
    ‖originalFullL2Parity x‖ = ‖x‖ := by
  exact (originalFullL2Parity (N := N)).norm_map x

/-- Original sixteen independent charge outputs preserve their full
finite Hilbert direct-sum squared-norm under the actual L2 isometry.
This identity is the analytic prerequisite for the true PiLp 2 map. -/
theorem originalChargeOutput_normSum_parity {N : ℕ}
    (y : SpinIndex → FullL2 N) :
    (∑ α : SpinIndex, ‖originalFullL2Parity (y α)‖ ^ 2) =
      ∑ α : SpinIndex, ‖y α‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro α _
  rw [originalFullL2Parity_norm (y α)]

/-- Original 1/16 physical source charge-column quadratic output
energy on a graph's second component. No replacement Hamiltonian. -/
def originalChargeOutputEnergy {N : ℕ}
    (y : SpinIndex → FullL2 N) : ℝ :=
  (1 / 16 : ℝ) * ∑ α : SpinIndex, ‖y α‖ ^ 2

/-- The manuscript/source's precise 1/16 normalization survives
simultaneous parity of all sixteen closed-graph charge outputs. -/
theorem originalChargeOutputEnergy_parity {N : ℕ}
    (y : SpinIndex → FullL2 N) :
    originalChargeOutputEnergy
      (fun α => originalFullL2Parity (y α)) =
      originalChargeOutputEnergy y := by
  unfold originalChargeOutputEnergy
  rw [originalChargeOutput_normSum_parity]

/-- For the genuine original source restricted, CLOSED physical graph,
parity carries the actual graph point into the exact opposite-gamma
restricted closed graph AND preserves its 1/16 sixteen-output energy. -/
theorem originalPhysicalClosedGraph_energy_parity {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    (x : FullL2 N) (y : SpinIndex → FullL2 N)
    (hxy : (x,y) ∈ closure (originalPhysicalCoreGraphSet M G)) :
    (originalFullL2Parity x,
        fun α => originalFullL2Parity (y α)) ∈
      closure (originalPhysicalCoreGraphSet (oppositeGamma M)
        (originalOppositeGammaGaugeData M G)) ∧
      originalChargeOutputEnergy (fun α => originalFullL2Parity (y α)) =
        originalChargeOutputEnergy y := by
  exact ⟨(originalPhysicalClosedGraph_mem_iff M G x y).mp hxy,
    originalChargeOutputEnergy_parity y⟩

#print axioms originalFullL2Parity_norm
#print axioms originalChargeOutput_normSum_parity
#print axioms originalChargeOutputEnergy
#print axioms originalChargeOutputEnergy_parity
#print axioms originalPhysicalClosedGraph_energy_parity

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AS
