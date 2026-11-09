import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4E3D2IndependentHistoricalTrueSquareDomain
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4D4BActualNativeAdjointSquareAction

/-!
BFSS M4F9 H4E3D3 — prospective independent physical Hilbert
adjoint-square action identified with the source historical D2B28
Hamiltonian after the authentic physical-input unitary.

Uses the already strict H4D4B native/independent adjoint-square
action intertwining and H4E3B2 original native/historical action,
with exact complex-linear scalar (1/16). No additional hypothesis,
proxy operator, or claim about spectrum or BFSS mass gap.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace FCP.M4F9H4E3D3IndependentHistoricalTrueSquareAction
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6H5E8BB
open FCP.BFSSSU2PhysicalDomainD2B28
open FCP.IndependentPhysicalSpace
open FCP.M4F9H2CActualE2NativeHilbertChargeColumn
open FCP.M4F9H3B2OriginalAYNativePhysicalHilbertChargeColumn
open MeasureTheory Set

/-- Generic normalized complex-Hilbert unitary transport.
Keep the 1/16 linearity proof OUT of the huge concrete AY source type. -/
private theorem normalizedIsometryIntertwine
    {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (U : X ≃ₗᵢ[ℂ] Y) {a : X} {b : Y} (h : b = U a) :
    (1 / 16 : ℂ) • b = U ((1 / 16 : ℂ) • a) := by
  calc
    (1 / 16 : ℂ) • b = (1 / 16 : ℂ) • U a :=
      congrArg ((1 / 16 : ℂ) • ·) h
    _ = U ((1 / 16 : ℂ) • a) := (map_smul U (1 / 16 : ℂ) a).symm

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

/-- Exact historical paired SU2 Hamiltonian action after the
original independent-to-source physical Hilbert unitary.
Every independent charge and adjoint input natural-domain witness
is explicit; the actual historical-domain witness is constructed
rather than assumed. Source-normalization is exactly 1/16. -/
theorem independentNativeAdjointSquare_action_historical :
    letI : CompleteSpace (independentPhysicalSpace theta hCAR hHermitian) :=
      FCP.M4F9H4D3AIndependentPhysicalHilbertComplete.independentPhysicalSpace_complete
        theta hCAR hHermitian J hJ
    letI : CompleteSpace pairedGaugeData.physicalSpace :=
      originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData
    ∀ (x : independentPhysicalSpace theta hCAR hHermitian)
      (hx : x ∈ (independentActualE2NativeHilbertChargeColumn
        theta hCAR hHermitian color gamma).domain)
      (hFx : (independentActualE2NativeHilbertChargeColumn
        theta hCAR hHermitian color gamma) ⟨x,hx⟩ ∈
        (independentActualE2NativeHilbertChargeColumn
          theta hCAR hHermitian color gamma).adjoint.domain),
    ∃ hh : independentPhysicalUnitary
          theta hCAR hHermitian J hJ x ∈ pairedSU2PhysicalHamiltonian.domain,
      pairedSU2PhysicalHamiltonian
          ⟨independentPhysicalUnitary theta hCAR hHermitian J hJ x,hh⟩ =
        independentPhysicalUnitary theta hCAR hHermitian J hJ
          ((1 / 16 : ℂ) •
            ((independentActualE2NativeHilbertChargeColumn
                theta hCAR hHermitian color gamma).adjoint
              ⟨(independentActualE2NativeHilbertChargeColumn
                  theta hCAR hHermitian color gamma) ⟨x,hx⟩,hFx⟩)) := by
  refine
    (letI : CompleteSpace (independentPhysicalSpace theta hCAR hHermitian) :=
       FCP.M4F9H4D3AIndependentPhysicalHilbertComplete.independentPhysicalSpace_complete
         theta hCAR hHermitian J hJ;
     letI : CompleteSpace pairedGaugeData.physicalSpace :=
       originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData;
     ?_)
  intro x hx hFx
  let f := independentActualE2NativeHilbertChargeColumn
    theta hCAR hHermitian color gamma
  let g := pairedOriginalNativePhysicalHilbertChargeColumn
  let U := independentPhysicalUnitary theta hCAR hHermitian J hJ
  obtain ⟨hz,hGx,hAdjAction⟩ :=
    FCP.M4F9H4D4BActualNativeAdjointSquareAction.nativeAdjointSquare_action_intertwine
      theta hCAR hHermitian color gamma J hColor hGamma hJ x hx hFx
  obtain ⟨hh,hHistAction⟩ :=
    FCP.M4F9H4E3B2GenericAdjointWeakFormHistoricalAction.pairedNativeAdjointSquare_action_eq_historical
      theta hCAR hHermitian color gamma J hColor hGamma hJ (U x) hz hGx
  have hNormalized :
      (1 / 16 : ℂ) • g.adjoint ⟨g ⟨U x,hz⟩,hGx⟩ =
        U ((1 / 16 : ℂ) • f.adjoint ⟨f ⟨x,hx⟩,hFx⟩) :=
    normalizedIsometryIntertwine U hAdjAction
  refine ⟨hh, ?_⟩
  exact hHistAction.trans hNormalized

#print axioms independentNativeAdjointSquare_action_historical
end
end FCP.M4F9H4E3D3IndependentHistoricalTrueSquareAction
