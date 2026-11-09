import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4D3CActualNativeAdjointReverse

/-!
BFSS M4F9 H4D3D — actual independent E2 and original AY NATIVE
Hilbert charge adjoint EXACT NATURAL-DOMAIN equivalence. The operators f and g
are the previously accepted original definitions, not aliases
defined by transport. Qualified actual native H4D3B forward and H4D3C reverse are composed
with actual H2D2A/H4D1 density, H4C2C natural domain iff,
H4C2D sixteen-charge action, and H4D3A true completeness.
No new charge is manufactured by transport; a fresh strict gate is required.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H4D3DActualNativeAdjointDomainIff
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

/-- Exact true-domain equivalence for the ACTUAL native Hilbert adjoints.
This combines both already strictly accepted actual BFSS Hilbert
adjoint transport theorems, not merely the generic covariance results. -/
theorem nativeAdjoint_domain_iff :
    letI : CompleteSpace (independentPhysicalSpace theta hCAR hHermitian) :=
      FCP.M4F9H4D3AIndependentPhysicalHilbertComplete.independentPhysicalSpace_complete
        theta hCAR hHermitian J hJ
    letI : CompleteSpace pairedGaugeData.physicalSpace :=
      FCP.BFSSSU2PhysicalDomainL6H5E8BB.originalPhysicalHilbertComplete
        pairedAlgebraData pairedGaugeData
    ∀ (y : PiLp 2 (fun _ : SpinIndex =>
        independentPhysicalSpace theta hCAR hHermitian)),
      y ∈ (independentActualE2NativeHilbertChargeColumn
        theta hCAR hHermitian color gamma).adjoint.domain ↔
        independentPhysicalHilbertOutputUnitary
          theta hCAR hHermitian J hJ y ∈
          pairedOriginalNativePhysicalHilbertChargeColumn.adjoint.domain := by
  intro y
  constructor
  · intro hy
    exact (FCP.M4F9H4D3BActualNativeAdjointForward.nativeAdjoint_forward_domain_action
      theta hCAR hHermitian color gamma J hColor hGamma hJ y hy).choose
  · intro hVy
    have hBack :=
      (FCP.M4F9H4D3CActualNativeAdjointReverse.nativeAdjoint_reverse_domain_action
        theta hCAR hHermitian color gamma J hColor hGamma hJ
        (independentPhysicalHilbertOutputUnitary theta hCAR hHermitian J hJ y)
        hVy).choose
    simpa only [
      (independentPhysicalHilbertOutputUnitary
        theta hCAR hHermitian J hJ).symm_apply_apply y] using hBack

#print axioms nativeAdjoint_domain_iff
end
end FCP.M4F9H4D3DActualNativeAdjointDomainIff
