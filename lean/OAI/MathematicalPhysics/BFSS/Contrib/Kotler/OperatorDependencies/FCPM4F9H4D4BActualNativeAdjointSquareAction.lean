import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4D4AActualNativeAdjointSquareDomain

/-!
BFSS M4F9 H4D4B: ACTUAL native AY and independently defined E2
Hilbert sixteen-charge ADJOINT-SQUARE action on the exact two-stage
natural domain accepted at H4D4A.

No invented globally defined `LinearPMap.comp`: the full natural
domain requires x ∈ T.domain AND T x ∈ T.adjoint.domain.
No historical ambient-output AY normalized Hamiltonian is identified.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace FCP.M4F9H4D4BActualNativeAdjointSquareAction
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

/-- The ACTUAL AY source-native and independent E2 native charge
Hilbert adjoint squares have the same action under the original
physical-input unitary U, on their genuine two-stage natural domains.
The existential produces all original AY charge/adjoint witnesses,
without presuming that either first charge maps its entire domain
into its Hilbert adjoint domain. -/
theorem nativeAdjointSquare_action_intertwine :
    letI : CompleteSpace (independentPhysicalSpace theta hCAR hHermitian) :=
      FCP.M4F9H4D3AIndependentPhysicalHilbertComplete.independentPhysicalSpace_complete
        theta hCAR hHermitian J hJ
    letI : CompleteSpace pairedGaugeData.physicalSpace :=
      FCP.BFSSSU2PhysicalDomainL6H5E8BB.originalPhysicalHilbertComplete
        pairedAlgebraData pairedGaugeData
    ∀ (x : independentPhysicalSpace theta hCAR hHermitian)
      (hx : x ∈ (independentActualE2NativeHilbertChargeColumn
        theta hCAR hHermitian color gamma).domain)
      (hFx : (independentActualE2NativeHilbertChargeColumn
          theta hCAR hHermitian color gamma) ⟨x,hx⟩ ∈
        (independentActualE2NativeHilbertChargeColumn
          theta hCAR hHermitian color gamma).adjoint.domain),
      ∃ (hz : independentPhysicalUnitary
          theta hCAR hHermitian J hJ x ∈
          pairedOriginalNativePhysicalHilbertChargeColumn.domain),
        ∃ (hGx : pairedOriginalNativePhysicalHilbertChargeColumn
            ⟨independentPhysicalUnitary
              theta hCAR hHermitian J hJ x,hz⟩ ∈
            pairedOriginalNativePhysicalHilbertChargeColumn.adjoint.domain),
          pairedOriginalNativePhysicalHilbertChargeColumn.adjoint
            ⟨pairedOriginalNativePhysicalHilbertChargeColumn
              ⟨independentPhysicalUnitary theta hCAR hHermitian J hJ x,hz⟩,
              hGx⟩ =
            independentPhysicalUnitary theta hCAR hHermitian J hJ
              ((independentActualE2NativeHilbertChargeColumn
                theta hCAR hHermitian color gamma).adjoint
                ⟨(independentActualE2NativeHilbertChargeColumn
                    theta hCAR hHermitian color gamma) ⟨x,hx⟩,hFx⟩) := by
  refine
    (letI : CompleteSpace (independentPhysicalSpace theta hCAR hHermitian) :=
       FCP.M4F9H4D3AIndependentPhysicalHilbertComplete.independentPhysicalSpace_complete
         theta hCAR hHermitian J hJ;
     letI : CompleteSpace pairedGaugeData.physicalSpace :=
       FCP.BFSSSU2PhysicalDomainL6H5E8BB.originalPhysicalHilbertComplete
         pairedAlgebraData pairedGaugeData;
     ?_)
  intro x hx hFx
  let f := independentActualE2NativeHilbertChargeColumn
    theta hCAR hHermitian color gamma
  let g := pairedOriginalNativePhysicalHilbertChargeColumn
  let U := independentPhysicalUnitary theta hCAR hHermitian J hJ
  let V := independentPhysicalHilbertOutputUnitary
    theta hCAR hHermitian J hJ
  have hSquared :
      ∃ hz : U x ∈ g.domain,
        g ⟨U x,hz⟩ ∈ g.adjoint.domain :=
    (FCP.M4F9H4D4AActualNativeAdjointSquareDomain.nativeAdjointSquare_naturalDomain_iff
      theta hCAR hHermitian color gamma J hColor hGamma hJ x).mp ⟨hx,hFx⟩
  obtain ⟨hz,hGx⟩ := hSquared
  have hChargeAction :
      V (f ⟨x,hx⟩) = g ⟨U x,hz⟩ := by
    simpa only [f,g,U,V] using
      (FCP.M4F9H4C2DExactNativeChargeAction.nativePhysicalCharge_action_intertwine
        theta hCAR hHermitian color gamma J hColor hGamma hJ x hx)
  obtain ⟨hVy,hAdjAction⟩ :=
    FCP.M4F9H4D3BActualNativeAdjointForward.nativeAdjoint_forward_domain_action
      theta hCAR hHermitian color gamma J hColor hGamma hJ
      (f ⟨x,hx⟩) hFx
  refine ⟨hz,hGx,?_⟩
  change g.adjoint ⟨g ⟨U x,hz⟩,hGx⟩ =
    U (f.adjoint ⟨f ⟨x,hx⟩,hFx⟩)
  have hArgEq :
      (⟨V (f ⟨x,hx⟩),hVy⟩ : g.adjoint.domain) =
      ⟨g ⟨U x,hz⟩,hGx⟩ :=
    Subtype.ext hChargeAction
  calc
    g.adjoint ⟨g ⟨U x,hz⟩,hGx⟩ =
        g.adjoint ⟨V (f ⟨x,hx⟩),hVy⟩ :=
      congrArg (fun w : g.adjoint.domain => g.adjoint w) hArgEq.symm
    _ = U (f.adjoint ⟨f ⟨x,hx⟩,hFx⟩) := hAdjAction

#print axioms nativeAdjointSquare_action_intertwine
end
end FCP.M4F9H4D4BActualNativeAdjointSquareAction
