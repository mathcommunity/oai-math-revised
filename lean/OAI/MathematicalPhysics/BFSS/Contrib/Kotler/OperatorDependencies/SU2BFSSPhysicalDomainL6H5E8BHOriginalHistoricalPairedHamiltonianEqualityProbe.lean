import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8BGOriginalHistoricalPhysicalHilbertChargeEqualityProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B28ConcretePairedSU2HamiltonianProbe

/-!
# H5E8BH — source-original AY/BE vs historical D2B17–28 Hamiltonian identification

PROSPECTIVE: unqualified until strict pinned Lean and source-axiom CI passes.
BG proved equality of ACTUAL AY original physical charge and historical
D2B17 native Hilbert LinearPMaps including full graph and domain.
Here we prove equality of true Hilbert adjoints, natural-domain T†T,
normalized (1/16)T†T operators and the concrete paired source Hamiltonian.

Historical D2B18 and BC independently implement natural-domain
composition; do not assume the false full-domain invariance of T.
Original signs/gamma, source spin-index and gauge action unchanged.
This does NOT prove the paper's independent arbitrary Cl(48)/Spin(48)
representation intertwiner, positive eigenvalues or BFSS mass gap.
-/

set_option autoImplicit false
set_option maxHeartbeats 240000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8BH
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AY
open FCP.BFSSSU2PhysicalDomainL6H5E8BB
open FCP.BFSSSU2PhysicalDomainL6H5E8BC
open FCP.BFSSSU2PhysicalDomainL6H5E8BE
open FCP.BFSSSU2PhysicalDomainL6H5E8BF
open FCP.BFSSSU2PhysicalDomainL6H5E8BG
open FCP.BFSSSU2PhysicalDomainD2B17
open FCP.BFSSSU2PhysicalDomainD2B18
open FCP.BFSSSU2PhysicalDomainD2B27
open FCP.BFSSSU2PhysicalDomainD2B28
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4J

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- Actual adjoints of identical densely-defined unbounded Hilbert
charge operators are equal on their full natural domains. -/
theorem originalMinimalPhysicalHilbertChargeAdjoint_eq_historical :
    originalMinimalPhysicalHilbertChargeAdjoint M G =
      sourceOriginalPhysicalChargeAdjoint M G := by
  let : CompleteSpace G.physicalSpace :=
    originalPhysicalHilbertComplete M G
  change (originalMinimalPhysicalHilbertChargeColumn M G).adjoint =
    (sourcePhysicalHilbertChargeColumn M G).adjoint
  rw [originalMinimalPhysicalHilbertChargeColumn_eq_historical M G]

theorem originalMinimalPhysicalHilbertChargeAdjoint_domain_eq_historical :
    (originalMinimalPhysicalHilbertChargeAdjoint M G).domain =
      (sourceOriginalPhysicalChargeAdjoint M G).domain := by
  rw [originalMinimalPhysicalHilbertChargeAdjoint_eq_historical M G]

/-- Equality includes the actual two-layer natural-domain T†T
partial-operator graph, not merely a formal core expression. -/
theorem originalMinimalPhysicalHilbertChargeAdjointSquare_eq_historical :
    originalMinimalPhysicalHilbertChargeAdjointSquare M G =
      sourcePhysicalChargeAdjointSquare M G := by
  change FCP.BFSSSU2PhysicalDomainL6H5E8BC.naturalComp
      (originalMinimalPhysicalHilbertChargeAdjoint M G)
      (originalMinimalPhysicalHilbertChargeColumn M G) =
    FCP.BFSSSU2PhysicalDomainD2B18.naturalComp
      (sourceOriginalPhysicalChargeAdjoint M G)
      (sourcePhysicalHilbertChargeColumn M G)
  rw [originalMinimalPhysicalHilbertChargeAdjoint_eq_historical M G,
    originalMinimalPhysicalHilbertChargeColumn_eq_historical M G]
  rfl

theorem originalMinimalPhysicalHilbertChargeAdjointSquare_domain_eq_historical :
    (originalMinimalPhysicalHilbertChargeAdjointSquare M G).domain =
      (sourcePhysicalChargeAdjointSquare M G).domain := by
  rw [originalMinimalPhysicalHilbertChargeAdjointSquare_eq_historical M G]

/-- Exact native original and historical 1/16 Hamiltonian partial
operators coincide on their entire natural domains. -/
theorem originalMinimalPhysicalNormalizedHamiltonian_eq_historical :
    originalMinimalPhysicalNormalizedHamiltonian M G =
      sourcePhysicalNormalizedHamiltonian M G := by
  change (1 / 16 : ℂ) • originalMinimalPhysicalHilbertChargeAdjointSquare M G =
    (1 / 16 : ℂ) • sourcePhysicalChargeAdjointSquare M G
  rw [originalMinimalPhysicalHilbertChargeAdjointSquare_eq_historical M G]

theorem originalMinimalPhysicalNormalizedHamiltonian_domain_eq_historical :
    (originalMinimalPhysicalNormalizedHamiltonian M G).domain =
      (sourcePhysicalNormalizedHamiltonian M G).domain := by
  rw [originalMinimalPhysicalNormalizedHamiltonian_eq_historical M G]

/-- Concrete paired 48-Majorana/24-boson original and historical
D2B28 source Hamiltonians are identical native Hilbert operators. -/
theorem pairedOriginalPhysicalNormalizedHamiltonian_eq_historical :
    pairedOriginalPhysicalNormalizedHamiltonian =
      pairedSU2PhysicalHamiltonian := by
  exact originalMinimalPhysicalNormalizedHamiltonian_eq_historical
    pairedAlgebraData pairedGaugeData

#print axioms originalMinimalPhysicalHilbertChargeAdjoint_eq_historical
#print axioms originalMinimalPhysicalHilbertChargeAdjoint_domain_eq_historical
#print axioms originalMinimalPhysicalHilbertChargeAdjointSquare_eq_historical
#print axioms originalMinimalPhysicalHilbertChargeAdjointSquare_domain_eq_historical
#print axioms originalMinimalPhysicalNormalizedHamiltonian_eq_historical
#print axioms originalMinimalPhysicalNormalizedHamiltonian_domain_eq_historical
#print axioms pairedOriginalPhysicalNormalizedHamiltonian_eq_historical

end
end FCP.BFSSSU2PhysicalDomainL6H5E8BH
