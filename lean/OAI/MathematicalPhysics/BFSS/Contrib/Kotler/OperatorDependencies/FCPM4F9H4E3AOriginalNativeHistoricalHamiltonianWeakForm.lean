import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4E2BOriginalAYAmbientNativeFullDomainForm
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8BHOriginalHistoricalPairedHamiltonianEqualityProbe

/-!
BFSS M4F9 H4E3A — PROSPECTIVE, NOT ACCEPTED before a strict gate.
Bridge the exact native AY sixteen-charge normalized weak form to
the ACTUAL historical D2B28 paired SU2 source Hamiltonian, by
composing the accepted source form characterization (H1 / BF / BH)
with the H4E2B full ambient/native charge domain and polarized form.

Retain H3B2 matching witnesses explicitly. Neither a new operator,
a false onto-ambient unitary, nor a spectral/eigenvalue theorem.
Do NOT use this before strict H4E2B and qualified source Hamiltonian
ancestry are both imported and axiom checked in one current gate.
-/
set_option autoImplicit false
set_option maxHeartbeats 240000

namespace FCP.M4F9H4E3AOriginalNativeHistoricalHamiltonianWeakForm
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6H5E8AY
open FCP.M4F9H3B2OriginalAYNativePhysicalHilbertChargeColumn
open FCP.M4F9H4E2BOriginalAYAmbientNativeFullDomainForm
open FCP.BFSSSU2PhysicalDomainL6H5E8BF
open FCP.BFSSSU2PhysicalDomainL6H5E8BH
open FCP.BFSSSU2PhysicalDomainD2B28
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

/-- Every normalized weak-form test on the TRUE native AY charge
domain is equivalent to testing the unchanged actual original
ambient AY source charge domain. No restricted core approximation. -/
theorem pairedOriginalNativeWeakForm_iff_ambient
    (u : pairedGaugeData.physicalSpace)
    (hu : u ∈ pairedOriginalNativePhysicalHilbertChargeColumn.domain)
    (w : pairedGaugeData.physicalSpace) :
    (∀ v : pairedOriginalNativePhysicalHilbertChargeColumn.domain,
      inner ℂ w (v : pairedGaugeData.physicalSpace) =
        (1 / 16 : ℂ) * inner ℂ
          (pairedOriginalNativePhysicalHilbertChargeColumn ⟨u,hu⟩)
          (pairedOriginalNativePhysicalHilbertChargeColumn v)) ↔
    (∀ v : (originalMinimalPhysicalHilbertChargeColumn
        pairedAlgebraData pairedGaugeData).domain,
      inner ℂ w (v : pairedGaugeData.physicalSpace) =
        (1 / 16 : ℂ) * inner ℂ
          ((originalMinimalPhysicalHilbertChargeColumn
            pairedAlgebraData pairedGaugeData)
            ⟨u, (pairedOriginalAYAmbientNative_fullNaturalDomain_iff
              theta hCAR hHermitian color gamma J hColor hGamma hJ u).mpr hu⟩)
          ((originalMinimalPhysicalHilbertChargeColumn
            pairedAlgebraData pairedGaugeData) v)) := by
  have hau : u ∈ (originalMinimalPhysicalHilbertChargeColumn
      pairedAlgebraData pairedGaugeData).domain :=
    (pairedOriginalAYAmbientNative_fullNaturalDomain_iff
      theta hCAR hHermitian color gamma J hColor hGamma hJ u).mpr hu
  constructor
  · intro hn v
    have hvn : (v : pairedGaugeData.physicalSpace) ∈
        pairedOriginalNativePhysicalHilbertChargeColumn.domain :=
      (pairedOriginalAYAmbientNative_fullNaturalDomain_iff
        theta hCAR hHermitian color gamma J hColor hGamma hJ
          (v : pairedGaugeData.physicalSpace)).mp v.property
    have hw := hn ⟨(v : pairedGaugeData.physicalSpace),hvn⟩
    have hf := pairedOriginalAYAmbientNative_normalizedForm_onAmbientDomain
      theta hCAR hHermitian color gamma J hColor hGamma hJ
      u (v : pairedGaugeData.physicalSpace) hau v.property
    exact hw.trans hf.symm
  · intro ha v
    have hva : (v : pairedGaugeData.physicalSpace) ∈
        (originalMinimalPhysicalHilbertChargeColumn
          pairedAlgebraData pairedGaugeData).domain :=
      (pairedOriginalAYAmbientNative_fullNaturalDomain_iff
        theta hCAR hHermitian color gamma J hColor hGamma hJ
          (v : pairedGaugeData.physicalSpace)).mpr v.property
    have hw := ha ⟨(v : pairedGaugeData.physicalSpace),hva⟩
    have hf := pairedOriginalAYAmbientNative_normalizedForm_onAmbientDomain
      theta hCAR hHermitian color gamma J hColor hGamma hJ
      u (v : pairedGaugeData.physicalSpace) hau hva
    exact hw.trans hf

/-- Exact Riesz weak-form characterization of the original historical
normalized SU2 Hamiltonian, but with TEST VECTORS AND CHARGE OUTPUTS
from the true native physical Hilbert charge domain. -/
theorem pairedOriginalNativeWeakForm_iff_historicalHamiltonian
    (u : pairedGaugeData.physicalSpace)
    (hu : u ∈ pairedOriginalNativePhysicalHilbertChargeColumn.domain)
    (w : pairedGaugeData.physicalSpace) :
    (∀ v : pairedOriginalNativePhysicalHilbertChargeColumn.domain,
      inner ℂ w (v : pairedGaugeData.physicalSpace) =
        (1 / 16 : ℂ) * inner ℂ
          (pairedOriginalNativePhysicalHilbertChargeColumn ⟨u,hu⟩)
          (pairedOriginalNativePhysicalHilbertChargeColumn v)) ↔
    (∃ hh : u ∈ pairedSU2PhysicalHamiltonian.domain,
      w = pairedSU2PhysicalHamiltonian ⟨u,hh⟩) := by
  have hau : u ∈ (originalMinimalPhysicalHilbertChargeColumn
      pairedAlgebraData pairedGaugeData).domain :=
    (pairedOriginalAYAmbientNative_fullNaturalDomain_iff
      theta hCAR hHermitian color gamma J hColor hGamma hJ u).mpr hu
  have hform := pairedOriginalNativeWeakForm_iff_ambient
    theta hCAR hHermitian color gamma J hColor hGamma hJ u hu w
  have hhistorical :=
    pairedOriginalPhysicalNormalizedHamiltonian_weakForm_iff ⟨u,hau⟩ w
  /- Avoid rewriting inside the entire dependent natural-domain
     proposition. Congruence on the exact BH source operator identity
     yields precisely the equality of *representing vector* properties. -/
  have hRepresentingVectorEq :
      (∃ h : u ∈ pairedOriginalPhysicalNormalizedHamiltonian.domain,
        w = pairedOriginalPhysicalNormalizedHamiltonian ⟨u,h⟩) =
      (∃ hh : u ∈ pairedSU2PhysicalHamiltonian.domain,
        w = pairedSU2PhysicalHamiltonian ⟨u,hh⟩) :=
    congrArg
      (fun T : pairedGaugeData.physicalSpace →ₗ.[ℂ]
          pairedGaugeData.physicalSpace =>
        ∃ h : u ∈ T.domain, w = T ⟨u,h⟩)
      pairedOriginalPhysicalNormalizedHamiltonian_eq_historical
  constructor
  · intro hn
    exact Eq.mp hRepresentingVectorEq (hhistorical.mp (hform.mp hn))
  · intro hh
    exact hform.mpr (hhistorical.mpr
      (Eq.mpr hRepresentingVectorEq hh))

#print axioms pairedOriginalNativeWeakForm_iff_ambient
#print axioms pairedOriginalNativeWeakForm_iff_historicalHamiltonian
end
end FCP.M4F9H4E3AOriginalNativeHistoricalHamiltonianWeakForm
