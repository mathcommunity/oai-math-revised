import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B27NormalizedHamiltonianSelfAdjointProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K2BNonzeroPhysicalL2Probe

/-!
# BFSS SU2 D2B28 — actual paired SU(2) gauge witness Hamiltonian specialization

PROSPECTIVE until exact pinned kernel/axiom CI gate passes.

G4-J constructed the literal SIX-FIELD original BFSS GaugeData for the
paired 48-Majorana/24-orbital concrete AlgebraData 2, with
genuine SU(2) bosonic/fermionic unitary gauge actions.
G4-K2B proved its physical Hilbert space is nonzero.

D2B27 established, for the exact original source charge model,
  H = (1/16) T†T,
its true IsSelfAdjoint proof on the correct natural domain,
and characterization as the unique weak-form representing-vector operator.
This module specializes those SAME declarations to the actual concrete
pairedAlgebraData and pairedGaugeData, rather than leaving them only
parameterized by arbitrary admissible source M and G.

This does NOT prove a unitary intertwiner with the INDEPENDENT paper's
arbitrary abstract irreducible Clifford module or its Spin(48) lift.
Do not transfer its positive-eigenvalue theorem without that bridge.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B28
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2GaugeG4K2B
open FCP.BFSSSU2PhysicalDomainD2B17
open FCP.BFSSSU2PhysicalDomainD2B27

/-- The exact original source-defined BFSS SU(2) normalized Hamiltonian
in the EXPLICIT paired 48-Majorana/24-orbital gauge representation. -/
noncomputable def pairedSU2PhysicalHamiltonian :
    pairedGaugeData.physicalSpace →ₗ.[ℂ] pairedGaugeData.physicalSpace :=
  sourcePhysicalNormalizedHamiltonian pairedAlgebraData pairedGaugeData

/-- The concrete physical Hilbert space is genuinely nonzero.
This uses the accepted original SU(2)-invariant radial L² wavepacket. -/
theorem pairedSU2PhysicalSpace_ne_bot :
    pairedGaugeData.physicalSpace ≠ (⊥ : Submodule ℂ (FullL2 2)) := by
  exact FCP.BFSSSU2GaugeG4K2B.pairedPhysicalSpace_ne_bot

/-- The Hamiltonian is GENUINELY self-adjoint on the concrete
original gauge-invariant Hilbert space and natural T†T domain. -/
theorem pairedSU2PhysicalHamiltonian_selfAdjoint :
    letI : CompleteSpace pairedGaugeData.physicalSpace :=
      sourceOriginalPhysicalHilbert_complete pairedAlgebraData pairedGaugeData
    IsSelfAdjoint pairedSU2PhysicalHamiltonian := by
  letI : CompleteSpace pairedGaugeData.physicalSpace :=
    sourceOriginalPhysicalHilbert_complete pairedAlgebraData pairedGaugeData
  exact sourcePhysicalNormalizedHamiltonian_selfAdjoint
    pairedAlgebraData pairedGaugeData

/-- Concrete SU(2) Hamiltonian is exactly the source normalized form's
associated operator, with correct source-domain/exact 1/16 coefficient. -/
theorem pairedSU2PhysicalHamiltonian_weakForm_iff
    (u : (sourcePhysicalHilbertChargeColumn
      pairedAlgebraData pairedGaugeData).domain)
    (w : pairedGaugeData.physicalSpace) :
    (∀ v : (sourcePhysicalHilbertChargeColumn
        pairedAlgebraData pairedGaugeData).domain,
      inner ℂ w (v : pairedGaugeData.physicalSpace) =
        (1 / 16 : ℂ) *
          inner ℂ (sourcePhysicalHilbertChargeColumn
            pairedAlgebraData pairedGaugeData u)
            (sourcePhysicalHilbertChargeColumn
              pairedAlgebraData pairedGaugeData v)) ↔
      ∃ h : (u : pairedGaugeData.physicalSpace) ∈
          pairedSU2PhysicalHamiltonian.domain,
        w = pairedSU2PhysicalHamiltonian ⟨u, h⟩ := by
  exact sourcePhysicalNormalizedHamiltonian_weakForm_iff
    pairedAlgebraData pairedGaugeData u w

theorem pairedSU2PhysicalHamiltonian_closed :
    pairedSU2PhysicalHamiltonian.IsClosed := by
  exact sourcePhysicalNormalizedHamiltonian_closed
    pairedAlgebraData pairedGaugeData

theorem pairedSU2PhysicalHamiltonian_domain_dense :
    Dense (pairedSU2PhysicalHamiltonian.domain :
      Set pairedGaugeData.physicalSpace) := by
  exact sourcePhysicalNormalizedHamiltonian_domain_dense
    pairedAlgebraData pairedGaugeData

#print axioms pairedSU2PhysicalSpace_ne_bot
#print axioms pairedSU2PhysicalHamiltonian_selfAdjoint
#print axioms pairedSU2PhysicalHamiltonian_weakForm_iff
#print axioms pairedSU2PhysicalHamiltonian_closed
#print axioms pairedSU2PhysicalHamiltonian_domain_dense

end
end FCP.BFSSSU2PhysicalDomainD2B28
