import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4E3AOriginalNativeHistoricalHamiltonianWeakForm
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4D1OriginalNativeHilbertChargeDomainDense

/-!
BFSS M4F9 H4E3B — prospective actual AY native adjoint-square/historical
SU2 Hamiltonian representing-vector equivalence and one-way action.

Use the unchanged source-native AY sixteen-charge partial operator and
its genuine Hilbert adjoint. Retain the true two-stage naturalComp
domain: x in T.domain AND T x in T.adjoint.domain.
The ambient/output inclusion is never treated as onto.
Source normalized form has exact 1/16 factor.
Every H3B2 representation-matching witness remains explicit.
UNQUALIFIED until exact pinned strict CI.
-/
set_option autoImplicit false
set_option maxHeartbeats 240000

namespace FCP.M4F9H4E3B1NativeActualAdjointSquareWeakRepresentative
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.M4F9H3B2OriginalAYNativePhysicalHilbertChargeColumn
open FCP.M4F9H4E3AOriginalNativeHistoricalHamiltonianWeakForm
open FCP.BFSSSU2PhysicalDomainL6H5E8BB
open FCP.BFSSSU2PhysicalDomainL6H5E8BC
open FCP.BFSSSU2PhysicalDomainL6H5E8BE
open FCP.BFSSSU2PhysicalDomainD2B28
open LinearPMap
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

/-- Exact weak-representative iff: the actual historical SU2
Hamiltonian and the normalized TRUE source-native AY adjoint square
have the same representing vector on the native charge natural
domain, without defining a substitute source Hamiltonian. -/
theorem pairedNativeNormalizedAdjointSquare_iff_historicalRepresentingVector :
    letI : CompleteSpace pairedGaugeData.physicalSpace :=
      originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData
    ∀ (u : pairedGaugeData.physicalSpace)
      (_hu : u ∈ pairedOriginalNativePhysicalHilbertChargeColumn.domain)
      (w : pairedGaugeData.physicalSpace),
    (∃ hs : u ∈ (naturalComp
          pairedOriginalNativePhysicalHilbertChargeColumn.adjoint
          pairedOriginalNativePhysicalHilbertChargeColumn).domain,
      w = (1 / 16 : ℂ) •
        (naturalComp
          pairedOriginalNativePhysicalHilbertChargeColumn.adjoint
          pairedOriginalNativePhysicalHilbertChargeColumn) ⟨u,hs⟩) ↔
    (∃ hh : u ∈ pairedSU2PhysicalHamiltonian.domain,
      w = pairedSU2PhysicalHamiltonian ⟨u,hh⟩) := by
  refine
    (letI : CompleteSpace pairedGaugeData.physicalSpace :=
       originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData;
     ?_)
  intro u hu w
  let g := pairedOriginalNativePhysicalHilbertChargeColumn
  have hd : Dense (g.domain : Set pairedGaugeData.physicalSpace) := by
    exact FCP.M4F9H4D1OriginalNativeHilbertChargeDomainDense.pairedOriginalNativePhysicalHilbertChargeColumn_domain_dense
      theta hCAR hHermitian color gamma J hColor hGamma hJ
  have hNormalized :
      (∀ v : g.domain,
        inner ℂ w (v : pairedGaugeData.physicalSpace) =
          (1 / 16 : ℂ) * inner ℂ (g ⟨u,hu⟩) (g v)) ↔
      (∃ hs : u ∈ (naturalComp g.adjoint g).domain,
        w = (1 / 16 : ℂ) • (naturalComp g.adjoint g) ⟨u,hs⟩) :=
    normalizedWeakRepresentative_iff_naturalAdjointSquare g hd ⟨u,hu⟩ w
  have hHistorical :=
    pairedOriginalNativeWeakForm_iff_historicalHamiltonian
      theta hCAR hHermitian color gamma J hColor hGamma hJ u hu w
  exact hNormalized.symm.trans hHistorical

#print axioms pairedNativeNormalizedAdjointSquare_iff_historicalRepresentingVector
end
end FCP.M4F9H4E3B1NativeActualAdjointSquareWeakRepresentative
