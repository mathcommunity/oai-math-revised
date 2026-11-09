import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4C2BExactNativeChargeGraphConjugacy

/-!
BFSS M4F9 H4C2C — EXACT native natural-domain correspondence
following a STRICTLY accepted two-sided graph iff of the ACTUAL
independent J-free E2 and original AY source physical Hilbert charge.
This is an operator-domain theorem only. No H, adjoint, spectrum.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H4C2CExactNativeChargeNaturalDomain
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open FCP.M4F9H2APhysicalHilbertOutputUnitary
open FCP.M4F9H2CActualE2NativeHilbertChargeColumn
open FCP.M4F9H3B2OriginalAYNativePhysicalHilbertChargeColumn
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
include color gamma hColor hGamma

/-- Actual independent E2 native Hilbert charge has exactly the
pullback of the actual original AY source-native charge domain
along the genuine physical input Hilbert unitary. -/
theorem nativeIndependentDomain_mem_iff_sourceDomain
    (u : independentPhysicalSpace theta hCAR hHermitian) :
    u ∈ (independentActualE2NativeHilbertChargeColumn
      theta hCAR hHermitian color gamma).domain ↔
      independentPhysicalUnitary theta hCAR hHermitian J hJ u ∈
        pairedOriginalNativePhysicalHilbertChargeColumn.domain := by
  constructor
  · intro hu
    obtain ⟨v,hv⟩ := (LinearPMap.mem_domain_iff).mp hu
    have hgraph :=
      (FCP.M4F9H4C2BExactNativeChargeGraphConjugacy.nativeIndependentGraph_mem_iff_sourceGraph
        theta hCAR hHermitian color gamma J hColor hGamma hJ (u,v)).mp hv
    exact (LinearPMap.mem_domain_iff).mpr
      ⟨independentPhysicalHilbertOutputUnitary
        theta hCAR hHermitian J hJ v, hgraph⟩
  · intro hu
    obtain ⟨v,hv⟩ := (LinearPMap.mem_domain_iff).mp hu
    let V := independentPhysicalHilbertOutputUnitary
      theta hCAR hHermitian J hJ
    have hgraph : (independentPhysicalUnitary
      theta hCAR hHermitian J hJ u, V (V.symm v)) ∈
      pairedOriginalNativePhysicalHilbertChargeColumn.graph := by
      simpa only [V.apply_symm_apply v] using hv
    have hind :=
      (FCP.M4F9H4C2BExactNativeChargeGraphConjugacy.nativeIndependentGraph_mem_iff_sourceGraph
        theta hCAR hHermitian color gamma J hColor hGamma hJ
        (u,V.symm v)).mpr hgraph
    exact (LinearPMap.mem_domain_iff).mpr ⟨V.symm v,hind⟩

#print axioms nativeIndependentDomain_mem_iff_sourceDomain
end
end FCP.M4F9H4C2CExactNativeChargeNaturalDomain
