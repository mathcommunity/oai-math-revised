import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4D3DActualNativeAdjointDomainIff

/-!
BFSS M4F9 H4D4A: exact natural input-domain equivalence of
the ACTUAL native AY and independent E2 unbounded adjoint squares.

The natural domain of T†T means:
  ∃ hx : x ∈ T.domain, T ⟨x,hx⟩ ∈ T.adjoint.domain.

IMPORTANT: this is NOT `LinearPMap.comp`, whose API requires
the first operator's entire domain to map into the second domain.
No alternate transported operator or ambient-output AY Hamiltonian
is created, and no unbounded square operator/action is yet claimed.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H4D4AActualNativeAdjointSquareDomain
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

/-- The actual natural input domains of the two native physical Hilbert
adjoint squares agree exactly under the existing physical-input unitary.
The existential conditions preserve both exact nested domains. -/
theorem nativeAdjointSquare_naturalDomain_iff :
    letI : CompleteSpace (independentPhysicalSpace theta hCAR hHermitian) :=
      FCP.M4F9H4D3AIndependentPhysicalHilbertComplete.independentPhysicalSpace_complete
        theta hCAR hHermitian J hJ
    letI : CompleteSpace pairedGaugeData.physicalSpace :=
      FCP.BFSSSU2PhysicalDomainL6H5E8BB.originalPhysicalHilbertComplete
        pairedAlgebraData pairedGaugeData
    ∀ (x : independentPhysicalSpace theta hCAR hHermitian),
      (∃ hx : x ∈ (independentActualE2NativeHilbertChargeColumn
          theta hCAR hHermitian color gamma).domain,
        (independentActualE2NativeHilbertChargeColumn
          theta hCAR hHermitian color gamma) ⟨x,hx⟩ ∈
          (independentActualE2NativeHilbertChargeColumn
            theta hCAR hHermitian color gamma).adjoint.domain)
      ↔ (∃ hz :
            independentPhysicalUnitary theta hCAR hHermitian J hJ x ∈
              pairedOriginalNativePhysicalHilbertChargeColumn.domain,
          pairedOriginalNativePhysicalHilbertChargeColumn
            ⟨independentPhysicalUnitary theta hCAR hHermitian J hJ x,hz⟩ ∈
              pairedOriginalNativePhysicalHilbertChargeColumn.adjoint.domain) := by
  refine
    (letI : CompleteSpace (independentPhysicalSpace theta hCAR hHermitian) :=
       FCP.M4F9H4D3AIndependentPhysicalHilbertComplete.independentPhysicalSpace_complete
         theta hCAR hHermitian J hJ;
     letI : CompleteSpace pairedGaugeData.physicalSpace :=
       FCP.BFSSSU2PhysicalDomainL6H5E8BB.originalPhysicalHilbertComplete
         pairedAlgebraData pairedGaugeData;
     ?_)
  intro x
  let f := independentActualE2NativeHilbertChargeColumn
    theta hCAR hHermitian color gamma
  let g := pairedOriginalNativePhysicalHilbertChargeColumn
  let U := independentPhysicalUnitary theta hCAR hHermitian J hJ
  let V := independentPhysicalHilbertOutputUnitary theta hCAR hHermitian J hJ
  have hChargeDomain : x ∈ f.domain ↔ U x ∈ g.domain := by
    simpa only [f,g,U] using
      (FCP.M4F9H4C2CExactNativeChargeNaturalDomain.nativeIndependentDomain_mem_iff_sourceDomain
        theta hCAR hHermitian color gamma J hColor hGamma hJ x)
  have hAdjDomain (w : PiLp 2 (fun _ : SpinIndex =>
      independentPhysicalSpace theta hCAR hHermitian)) :
      w ∈ f.adjoint.domain ↔ V w ∈ g.adjoint.domain := by
    simpa only [f,g,V] using
      (FCP.M4F9H4D3DActualNativeAdjointDomainIff.nativeAdjoint_domain_iff
        theta hCAR hHermitian color gamma J hColor hGamma hJ w)
  have hChargeAction (hx : x ∈ f.domain) (hz : U x ∈ g.domain) :
      V (f ⟨x,hx⟩) = g ⟨U x,hz⟩ := by
    simpa only [f,g,U,V] using
      (FCP.M4F9H4C2DExactNativeChargeAction.nativePhysicalCharge_action_intertwine
        theta hCAR hHermitian color gamma J hColor hGamma hJ x hx)
  change (∃ hx : x ∈ f.domain, f ⟨x,hx⟩ ∈ f.adjoint.domain) ↔
    (∃ hz : U x ∈ g.domain, g ⟨U x,hz⟩ ∈ g.adjoint.domain)
  constructor
  · rintro ⟨hx, hOut⟩
    have hz : U x ∈ g.domain := hChargeDomain.mp hx
    refine ⟨hz, ?_⟩
    have hVOut : V (f ⟨x,hx⟩) ∈ g.adjoint.domain :=
      (hAdjDomain (f ⟨x,hx⟩)).mp hOut
    simpa only [hChargeAction hx hz] using hVOut
  · rintro ⟨hz, hOut⟩
    have hx : x ∈ f.domain := hChargeDomain.mpr hz
    refine ⟨hx, ?_⟩
    have hVOut : V (f ⟨x,hx⟩) ∈ g.adjoint.domain := by
      simpa only [hChargeAction hx hz] using hOut
    exact (hAdjDomain (f ⟨x,hx⟩)).mpr hVOut

#print axioms nativeAdjointSquare_naturalDomain_iff
end
end FCP.M4F9H4D4AActualNativeAdjointSquareDomain
