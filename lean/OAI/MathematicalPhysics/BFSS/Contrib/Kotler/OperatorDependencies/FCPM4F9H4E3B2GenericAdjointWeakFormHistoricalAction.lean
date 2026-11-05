import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4E3B1NativeActualAdjointSquareWeakRepresentative
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4D1OriginalNativeHilbertChargeDomainDense

/-!
BFSS M4F9 H4E3B2 — prospective, not accepted.

Separate the generically typed normalized Hilbert adjoint identity
from the concrete source AY sixteen-charge operator. The source-specific
historical action is deduced from H4E3A's strictly qualified weak form.

Do not substitute a proxy charge or Hamiltonian. The original input u
is in the entire T_n charge domain and the charge output T_n u is in
the genuine Hilbert adjoint domain (true two-stage natural square).
-/
set_option autoImplicit false
set_option maxHeartbeats 240000

namespace FCP.M4F9H4E3B2GenericAdjointWeakFormHistoricalAction
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.M4F9H3B2OriginalAYNativePhysicalHilbertChargeColumn
open FCP.M4F9H4E3AOriginalNativeHistoricalHamiltonianWeakForm
open FCP.BFSSSU2PhysicalDomainL6H5E8BB
open FCP.BFSSSU2PhysicalDomainL6H5E8BE
open FCP.BFSSSU2PhysicalDomainD2B28
open MeasureTheory Set

variable {X Y : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

/-- Generic source-faithful normalized adjoint weak form. The
abstract types prevent Lean from unfolding the huge BFSS fiber
constructions during the complex normalization identity. -/
theorem genericNormalizedAdjointWeakForm
    (T : X →ₗ.[ℂ] Y) (hd : Dense (T.domain : Set X))
    (u : T.domain) (hOut : T u ∈ T.adjoint.domain) :
    ∀ v : T.domain,
      inner ℂ ((1 / 16 : ℂ) • T.adjoint ⟨T u,hOut⟩)
        (v : X) =
        (1 / 16 : ℂ) * inner ℂ (T u) (T v) := by
  intro v
  calc
    inner ℂ ((1 / 16 : ℂ) • T.adjoint ⟨T u,hOut⟩) (v : X) =
        (1 / 16 : ℂ) * inner ℂ (T.adjoint ⟨T u,hOut⟩) (v : X) :=
      one_sixteenth_inner_smul _ _
    _ = (1 / 16 : ℂ) * inner ℂ (T u) (T v) :=
      congrArg ((1 / 16 : ℂ) * ·)
        (LinearPMap.adjoint_isFormalAdjoint hd ⟨T u,hOut⟩ v)

#print axioms genericNormalizedAdjointWeakForm

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

/-- Actual original native AY Hilbert adjoint-square action agrees
with the historical D2B28 paired SU2 Hamiltonian, on the precise
two-stage natural domain; all source representation hypotheses explicit. -/
theorem pairedNativeAdjointSquare_action_eq_historical :
    letI : CompleteSpace pairedGaugeData.physicalSpace :=
      originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData
    ∀ (u : pairedGaugeData.physicalSpace)
      (hu : u ∈ pairedOriginalNativePhysicalHilbertChargeColumn.domain)
      (hOut : pairedOriginalNativePhysicalHilbertChargeColumn ⟨u,hu⟩ ∈
        pairedOriginalNativePhysicalHilbertChargeColumn.adjoint.domain),
    ∃ hh : u ∈ pairedSU2PhysicalHamiltonian.domain,
      pairedSU2PhysicalHamiltonian ⟨u,hh⟩ =
        (1 / 16 : ℂ) •
          (pairedOriginalNativePhysicalHilbertChargeColumn.adjoint
            ⟨pairedOriginalNativePhysicalHilbertChargeColumn ⟨u,hu⟩,hOut⟩) := by
  refine
    (letI : CompleteSpace pairedGaugeData.physicalSpace :=
       originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData;
     ?_)
  intro u hu hOut
  have hd :
      Dense (pairedOriginalNativePhysicalHilbertChargeColumn.domain :
        Set pairedGaugeData.physicalSpace) :=
    FCP.M4F9H4D1OriginalNativeHilbertChargeDomainDense.pairedOriginalNativePhysicalHilbertChargeColumn_domain_dense
      theta hCAR hHermitian color gamma J hColor hGamma hJ
  have hWeak : ∀ v : pairedOriginalNativePhysicalHilbertChargeColumn.domain,
      inner ℂ
        ((1 / 16 : ℂ) •
          (pairedOriginalNativePhysicalHilbertChargeColumn.adjoint
            ⟨pairedOriginalNativePhysicalHilbertChargeColumn ⟨u,hu⟩,hOut⟩))
        (v : pairedGaugeData.physicalSpace) =
      (1 / 16 : ℂ) *
        inner ℂ (pairedOriginalNativePhysicalHilbertChargeColumn ⟨u,hu⟩)
          (pairedOriginalNativePhysicalHilbertChargeColumn v) :=
    genericNormalizedAdjointWeakForm
      pairedOriginalNativePhysicalHilbertChargeColumn hd ⟨u,hu⟩ hOut
  obtain ⟨hh,hEq⟩ :=
    (pairedOriginalNativeWeakForm_iff_historicalHamiltonian
      theta hCAR hHermitian color gamma J hColor hGamma hJ u hu
      ((1 / 16 : ℂ) •
        (pairedOriginalNativePhysicalHilbertChargeColumn.adjoint
          ⟨pairedOriginalNativePhysicalHilbertChargeColumn ⟨u,hu⟩,hOut⟩))).mp hWeak
  exact ⟨hh,hEq.symm⟩

#print axioms pairedNativeAdjointSquare_action_eq_historical
end
end FCP.M4F9H4E3B2GenericAdjointWeakFormHistoricalAction
