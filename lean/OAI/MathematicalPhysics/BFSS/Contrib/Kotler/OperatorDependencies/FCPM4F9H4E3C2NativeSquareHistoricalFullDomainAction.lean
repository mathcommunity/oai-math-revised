import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4E3C1HistoricalDomainNativeCharge

/-!
BFSS M4F9 H4E3C2 — PROSPECTIVE, NOT STRICT QUALIFIED.

Actual original AY source native normalized adjoint square has exactly
the historical D2B28 paired SU2 Hamiltonian domain and action.
The true source-derived BC.naturalComp is preserved; its natural domain
consists of x in charge-domain AND T_n x in the Hilbert adjoint domain.

C1 must independently pass strict CI before this module may enter
a qualifying gate. Keep representation matching and exact 1/16 real
normalization, no false full-domain closed-product composition, no
surjectivity of native→ambient output isometry, no spectral claim.
-/
set_option autoImplicit false
set_option maxHeartbeats 240000

namespace FCP.M4F9H4E3C2NativeSquareHistoricalFullDomainAction
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6H5E8BB
open FCP.BFSSSU2PhysicalDomainL6H5E8BC
open FCP.BFSSSU2PhysicalDomainD2B28
open FCP.M4F9H3B2OriginalAYNativePhysicalHilbertChargeColumn
open FCP.M4F9H4E3B1NativeActualAdjointSquareWeakRepresentative
open FCP.M4F9H4E3B2GenericAdjointWeakFormHistoricalAction
open FCP.M4F9H4E3C1HistoricalDomainNativeCharge
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

/-- Exact equality of historical Hamiltonian and true native
AY Hilbert charge adjoint-square natural domains. -/
theorem nativeNormalizedSquare_naturalDomain_iff_historical :
    letI : CompleteSpace pairedGaugeData.physicalSpace :=
      originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData
    ∀ (u : pairedGaugeData.physicalSpace),
      u ∈ (naturalComp
          pairedOriginalNativePhysicalHilbertChargeColumn.adjoint
          pairedOriginalNativePhysicalHilbertChargeColumn).domain ↔
      u ∈ pairedSU2PhysicalHamiltonian.domain := by
  refine
    (letI : CompleteSpace pairedGaugeData.physicalSpace :=
       originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData;
     ?_)
  intro u
  constructor
  · intro hSquare
    obtain ⟨hu,hOut⟩ := naturalComp_mem_domain.mp hSquare
    exact (pairedNativeAdjointSquare_action_eq_historical
      theta hCAR hHermitian color gamma J hColor hGamma hJ
      u hu hOut).choose
  · intro hh
    have hu : u ∈ pairedOriginalNativePhysicalHilbertChargeColumn.domain :=
      historicalHamiltonian_domain_subset_nativeCharge
        theta hCAR hHermitian color gamma J hColor hGamma hJ u hh
    have hRep := pairedNativeNormalizedAdjointSquare_iff_historicalRepresentingVector
      theta hCAR hHermitian color gamma J hColor hGamma hJ u hu
      (pairedSU2PhysicalHamiltonian ⟨u,hh⟩)
    obtain ⟨hs,_⟩ := hRep.mpr ⟨hh,rfl⟩
    exact hs

/-- Action of the actual source native adjoint-square and historical
Hamiltonian coincide for ALL compatible natural-domain witnesses,
including the exact 1/16 factor. -/
theorem nativeNormalizedSquare_fullAction_eq_historical :
    letI : CompleteSpace pairedGaugeData.physicalSpace :=
      originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData
    ∀ (u : pairedGaugeData.physicalSpace)
      (hs : u ∈ (naturalComp
        pairedOriginalNativePhysicalHilbertChargeColumn.adjoint
        pairedOriginalNativePhysicalHilbertChargeColumn).domain)
      (hh : u ∈ pairedSU2PhysicalHamiltonian.domain),
      (1 / 16 : ℂ) •
        (naturalComp
          pairedOriginalNativePhysicalHilbertChargeColumn.adjoint
          pairedOriginalNativePhysicalHilbertChargeColumn) ⟨u,hs⟩ =
        pairedSU2PhysicalHamiltonian ⟨u,hh⟩ := by
  refine
    (letI : CompleteSpace pairedGaugeData.physicalSpace :=
       originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData;
     ?_)
  intro u hs hh
  have hu : u ∈ pairedOriginalNativePhysicalHilbertChargeColumn.domain :=
    (naturalComp_mem_domain.mp hs).1
  have hRep := pairedNativeNormalizedAdjointSquare_iff_historicalRepresentingVector
    theta hCAR hHermitian color gamma J hColor hGamma hJ u hu
    ((1 / 16 : ℂ) •
      (naturalComp
        pairedOriginalNativePhysicalHilbertChargeColumn.adjoint
        pairedOriginalNativePhysicalHilbertChargeColumn) ⟨u,hs⟩)
  obtain ⟨hh2,hEq⟩ := hRep.mp ⟨hs,rfl⟩
  have heq :
      (⟨u,hh2⟩ : pairedSU2PhysicalHamiltonian.domain) =
        ⟨u,hh⟩ := Subtype.ext rfl
  exact hEq.trans (congrArg
    (fun z : pairedSU2PhysicalHamiltonian.domain =>
      pairedSU2PhysicalHamiltonian z) heq)

#print axioms nativeNormalizedSquare_naturalDomain_iff_historical
#print axioms nativeNormalizedSquare_fullAction_eq_historical
end
end FCP.M4F9H4E3C2NativeSquareHistoricalFullDomainAction
