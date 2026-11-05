import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4E2AOriginalAYAmbientNativePolarizedForm

/-!
BFSS M4F9 H4E2B — source ACTUAL ambient AY versus native physical-output
charge: full charge natural-domain correspondence and normalized polarized
form on the AMBIENT domain, with all H3B2 matching assumptions explicit.

Reuses strictly qualified H3B2 and H4E2A, not a recreated operator.
The native/ambient physical output inclusion remains an isometry into
FullL2, never a surjective unitary onto the ambient output space.
No adjoint-square/Hamiltonian equality, independent universal realization,
or spectral claim.
-/
set_option autoImplicit false
set_option maxHeartbeats 180000

namespace FCP.M4F9H4E2BOriginalAYAmbientNativeFullDomainForm
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6H5E8AY
open FCP.M4F9H3B2OriginalAYNativePhysicalHilbertChargeColumn
open FCP.M4F9H4E2AOriginalAYAmbientNativePolarizedForm
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

/-- Full, genuine AY ambient charge domain equals the native physical
charge natural domain. The ambient→native direction uses the separately
qualified H3A source graph output physicality under matching witnesses. -/
theorem pairedOriginalAYAmbientNative_fullNaturalDomain_iff
    (u : pairedGaugeData.physicalSpace) :
    u ∈ (originalMinimalPhysicalHilbertChargeColumn
      pairedAlgebraData pairedGaugeData).domain ↔
      u ∈ pairedOriginalNativePhysicalHilbertChargeColumn.domain := by
  exact (pairedOriginalNativePhysicalHilbertChargeColumn_domain_iff
    theta hCAR hHermitian color gamma J hColor hGamma hJ u).symm

/-- Equality of the exact source 1/16 polarized charge-energy forms on
the ENTIRE original ambient AY natural domain, not merely on a source
core or an assumed common domain. The H3B2 hypotheses are explicit. -/
theorem pairedOriginalAYAmbientNative_normalizedForm_onAmbientDomain
    (u v : pairedGaugeData.physicalSpace)
    (hu : u ∈ (originalMinimalPhysicalHilbertChargeColumn
      pairedAlgebraData pairedGaugeData).domain)
    (hv : v ∈ (originalMinimalPhysicalHilbertChargeColumn
      pairedAlgebraData pairedGaugeData).domain) :
    (1 / 16 : ℂ) *
      inner ℂ
        ((originalMinimalPhysicalHilbertChargeColumn
          pairedAlgebraData pairedGaugeData) ⟨u, hu⟩)
        ((originalMinimalPhysicalHilbertChargeColumn
          pairedAlgebraData pairedGaugeData) ⟨v, hv⟩) =
    (1 / 16 : ℂ) *
      inner ℂ
        (pairedOriginalNativePhysicalHilbertChargeColumn
          ⟨u, (pairedOriginalAYAmbientNative_fullNaturalDomain_iff
            theta hCAR hHermitian color gamma J hColor hGamma hJ u).mp hu⟩)
        (pairedOriginalNativePhysicalHilbertChargeColumn
          ⟨v, (pairedOriginalAYAmbientNative_fullNaturalDomain_iff
            theta hCAR hHermitian color gamma J hColor hGamma hJ v).mp hv⟩) := by
  have hun : u ∈ pairedOriginalNativePhysicalHilbertChargeColumn.domain :=
    (pairedOriginalAYAmbientNative_fullNaturalDomain_iff
      theta hCAR hHermitian color gamma J hColor hGamma hJ u).mp hu
  have hvn : v ∈ pairedOriginalNativePhysicalHilbertChargeColumn.domain :=
    (pairedOriginalAYAmbientNative_fullNaturalDomain_iff
      theta hCAR hHermitian color gamma J hColor hGamma hJ v).mp hv
  exact pairedOriginalAYAmbientNative_normalizedForm_eq u v hun hvn

#print axioms pairedOriginalAYAmbientNative_fullNaturalDomain_iff
#print axioms pairedOriginalAYAmbientNative_normalizedForm_onAmbientDomain
end
end FCP.M4F9H4E2BOriginalAYAmbientNativeFullDomainForm
