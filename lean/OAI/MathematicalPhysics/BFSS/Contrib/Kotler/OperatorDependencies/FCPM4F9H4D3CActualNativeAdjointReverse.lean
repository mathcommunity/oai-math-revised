import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4D3BActualNativeAdjointForward

/-!
BFSS M4F9 H4D3C — actual J-free E2 and original AY NATIVE
Hilbert charge adjoint REVERSE transport. The operators f and g
are the previously accepted original definitions, not aliases
defined by transport. Generic Hilbert adjoint H4D2B is instantiated
with actual H2D2A/H4D1 density, H4C2C natural domain iff,
H4C2D sixteen-charge action, and H4D3A true completeness.
This reverse specialization is a candidate until strict qualified CI.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H4D3CActualNativeAdjointReverse
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

/-- Genuine original AY source-native Hilbert adjoint reverse transport
into the ACTUAL independent J-free sixteen-charge Hilbert adjoint,
without modifying either originally defined charge. -/
theorem nativeAdjoint_reverse_domain_action :
    letI : CompleteSpace (independentPhysicalSpace theta hCAR hHermitian) :=
      FCP.M4F9H4D3AIndependentPhysicalHilbertComplete.independentPhysicalSpace_complete
        theta hCAR hHermitian J hJ
    letI : CompleteSpace pairedGaugeData.physicalSpace :=
      FCP.BFSSSU2PhysicalDomainL6H5E8BB.originalPhysicalHilbertComplete
        pairedAlgebraData pairedGaugeData
    ∀ (y : PiLp 2 (fun _ : SpinIndex => pairedGaugeData.physicalSpace))
      (hy : y ∈ pairedOriginalNativePhysicalHilbertChargeColumn.adjoint.domain),
    ∃ hVy : (independentPhysicalHilbertOutputUnitary
          theta hCAR hHermitian J hJ).symm y ∈
        (independentActualE2NativeHilbertChargeColumn
          theta hCAR hHermitian color gamma).adjoint.domain,
      (independentActualE2NativeHilbertChargeColumn
        theta hCAR hHermitian color gamma).adjoint
        ⟨(independentPhysicalHilbertOutputUnitary
          theta hCAR hHermitian J hJ).symm y,hVy⟩ =
        (independentPhysicalUnitary theta hCAR hHermitian J hJ).symm
          (pairedOriginalNativePhysicalHilbertChargeColumn.adjoint ⟨y,hy⟩) := by
  intro y hy
  let f := independentActualE2NativeHilbertChargeColumn
    theta hCAR hHermitian color gamma
  let g := pairedOriginalNativePhysicalHilbertChargeColumn
  let U := independentPhysicalUnitary theta hCAR hHermitian J hJ
  let V := independentPhysicalHilbertOutputUnitary
    theta hCAR hHermitian J hJ
  have hf : Dense (f.domain : Set (independentPhysicalSpace
      theta hCAR hHermitian)) :=
    FCP.M4F9H2D2ANativeHilbertE2ContinuityAndDensity.independentActualE2NativeHilbertChargeColumn_domain_dense
      theta hCAR hHermitian color gamma J hColor hGamma hJ
  have hg : Dense (g.domain : Set pairedGaugeData.physicalSpace) :=
    FCP.M4F9H4D1OriginalNativeHilbertChargeDomainDense.pairedOriginalNativePhysicalHilbertChargeColumn_domain_dense
      theta hCAR hHermitian color gamma J hColor hGamma hJ
  have hFwd : ∀ x : independentPhysicalSpace theta hCAR hHermitian,
      x ∈ f.domain → U x ∈ g.domain := by
    intro x hx
    exact (FCP.M4F9H4C2CExactNativeChargeNaturalDomain.nativeIndependentDomain_mem_iff_sourceDomain
      theta hCAR hHermitian color gamma J hColor hGamma hJ x).mp hx
  have hRev : ∀ z : pairedGaugeData.physicalSpace,
      z ∈ g.domain → U.symm z ∈ f.domain := by
    intro z hz
    apply (FCP.M4F9H4C2CExactNativeChargeNaturalDomain.nativeIndependentDomain_mem_iff_sourceDomain
      theta hCAR hHermitian color gamma J hColor hGamma hJ (U.symm z)).mpr
    change U (U.symm z) ∈ g.domain
    simpa only [U.apply_symm_apply z] using hz
  have hAct : ∀ x : f.domain,
      V (f x) = g ⟨U (x : independentPhysicalSpace
        theta hCAR hHermitian),hFwd (x : _) x.property⟩ := by
    intro x
    exact FCP.M4F9H4C2DExactNativeChargeAction.nativePhysicalCharge_action_intertwine
      theta hCAR hHermitian color gamma J hColor hGamma hJ
      (x : independentPhysicalSpace theta hCAR hHermitian) x.property
  simpa only [f,g,U,V] using
    (letI : CompleteSpace (independentPhysicalSpace theta hCAR hHermitian) :=
       FCP.M4F9H4D3AIndependentPhysicalHilbertComplete.independentPhysicalSpace_complete
         theta hCAR hHermitian J hJ;
     letI : CompleteSpace pairedGaugeData.physicalSpace :=
       FCP.BFSSSU2PhysicalDomainL6H5E8BB.originalPhysicalHilbertComplete
         pairedAlgebraData pairedGaugeData;
     FCP.M4F9H4D2BGenericNativeHilbertAdjointReverse.adjoint_reverse_domain_action
       f g U V hf hg hFwd hRev hAct y hy)

#print axioms nativeAdjoint_reverse_domain_action
end
end FCP.M4F9H4D3CActualNativeAdjointReverse
