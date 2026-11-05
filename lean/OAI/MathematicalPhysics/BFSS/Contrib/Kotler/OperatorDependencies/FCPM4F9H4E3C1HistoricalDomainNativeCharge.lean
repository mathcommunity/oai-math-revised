import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4E3B2GenericAdjointWeakFormHistoricalAction

/-!
BFSS M4F9 H4E3C1 — source-exact reverse historical-domain to
true original AY NATIVE sixteen-charge domain qualification.

The historical D2B28 paired SU2 Hamiltonian is literally the
accepted BH normalized original-source (1/16)T†T partial operator.
The source natural square domain is a subset of the SOURCE ambient
charge domain; the accepted H4E2B exact complete domain bridge
transports that membership to actual native physical-output AY T_n.

No proxy operator, false full-domain invariance, unqualified physical
output surjectivity, or spectral statement. Every H3B2 matching
hypothesis is explicit. Prospective until pinned strict CI.
-/
set_option autoImplicit false
set_option maxHeartbeats 240000

namespace FCP.M4F9H4E3C1HistoricalDomainNativeCharge
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6H5E8AY
open FCP.BFSSSU2PhysicalDomainL6H5E8BC
open FCP.BFSSSU2PhysicalDomainL6H5E8BE
open FCP.BFSSSU2PhysicalDomainL6H5E8BF
open FCP.BFSSSU2PhysicalDomainL6H5E8BH
open FCP.BFSSSU2PhysicalDomainD2B28
open FCP.M4F9H3B2OriginalAYNativePhysicalHilbertChargeColumn
open FCP.M4F9H4E2BOriginalAYAmbientNativeFullDomainForm
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
variable (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
variable (hCAR : ∀ α β A B,
  theta α A * theta β B + theta β B * theta α A =
    (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
variable (hHermitian : ∀ α A, (theta α A).IsSymmetric)
variable (color : ColorIndex 2 → ColorMatrix 2)
variable (gamma : SpaceIndex → GammaMatrix)
variable (J : E ≃ₗᵢ[ℂ] Fermion 2)
variable (hColor : color = pairedAlgebraData.color)
variable (hGamma : gamma = pairedAlgebraData.gamma)
variable (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
include theta hCAR hHermitian color gamma J hColor hGamma hJ

/-- Every vector in the historical actual source SU2 Hamiltonian
domain belongs to the ACTUAL AY native Hilbert sixteen-charge
domain. The source normalized Hamiltonian uses the exact two-stage
natural square domain, not all possible charge inputs. -/
theorem historicalHamiltonian_domain_subset_nativeCharge :
    ∀ (u : pairedGaugeData.physicalSpace),
      u ∈ pairedSU2PhysicalHamiltonian.domain →
        u ∈ pairedOriginalNativePhysicalHilbertChargeColumn.domain := by
  intro u hh
  have hOperatorDomains :
      pairedOriginalPhysicalNormalizedHamiltonian.domain =
        pairedSU2PhysicalHamiltonian.domain :=
    congrArg
      (fun T : pairedGaugeData.physicalSpace →ₗ.[ℂ]
          pairedGaugeData.physicalSpace => T.domain)
      pairedOriginalPhysicalNormalizedHamiltonian_eq_historical
  have hOrig : u ∈ pairedOriginalPhysicalNormalizedHamiltonian.domain := by
    rw [hOperatorDomains]
    exact hh
  have hSourceSquare : u ∈
      (originalMinimalPhysicalHilbertChargeAdjointSquare
        pairedAlgebraData pairedGaugeData).domain := by
    rw [← pairedOriginalPhysicalNormalizedHamiltonian_domain]
    exact hOrig
  have hSourceCharge : u ∈
      (originalMinimalPhysicalHilbertChargeColumn
        pairedAlgebraData pairedGaugeData).domain := by
    obtain ⟨hCharge,_⟩ :=
      (originalMinimalPhysicalHilbertChargeAdjointSquare_domain
        pairedAlgebraData pairedGaugeData u).mp hSourceSquare
    exact hCharge
  exact (pairedOriginalAYAmbientNative_fullNaturalDomain_iff
    theta hCAR hHermitian color gamma J hColor hGamma hJ u).mp hSourceCharge

#print axioms historicalHamiltonian_domain_subset_nativeCharge
end
end FCP.M4F9H4E3C1HistoricalDomainNativeCharge
