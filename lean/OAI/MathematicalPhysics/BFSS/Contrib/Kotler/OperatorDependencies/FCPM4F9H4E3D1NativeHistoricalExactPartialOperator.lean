import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4E3C2NativeSquareHistoricalFullDomainAction

/-!
BFSS M4F9 H4E3D1 — prospective exact partial operator equality.
Use source-qualified C2 full actual native adjoint-square domain iff and
all natural-domain action equality with literal historical D2B28 SU2 H.

No proxy Hamiltonian, closed-domain extension, normalization adjustment,
ambient output isometry surjectivity, or spectral assertion. Original
H3B2 representation matching retained. Pinned strict CI required.
-/
set_option autoImplicit false
set_option maxHeartbeats 240000

namespace FCP.M4F9H4E3D1NativeHistoricalExactPartialOperator
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6H5E8BB
open FCP.BFSSSU2PhysicalDomainL6H5E8BC
open FCP.BFSSSU2PhysicalDomainD2B28
open FCP.M4F9H3B2OriginalAYNativePhysicalHilbertChargeColumn
open FCP.M4F9H4E3C2NativeSquareHistoricalFullDomainAction
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

/-- The literal source-native normalized AY adjoint square as
a genuine unbounded Hilbert partial operator equals the unchanged
historical source D2B28 paired SU2 Hamiltonian. The entire true
natural domain and action agree, under explicit representation matching. -/
theorem pairedNativeNormalizedAdjointSquare_eq_historical :
    letI : CompleteSpace pairedGaugeData.physicalSpace :=
      originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData
    (1 / 16 : ℂ) •
      (naturalComp
        pairedOriginalNativePhysicalHilbertChargeColumn.adjoint
        pairedOriginalNativePhysicalHilbertChargeColumn) =
      pairedSU2PhysicalHamiltonian := by
  refine
    (letI : CompleteSpace pairedGaugeData.physicalSpace :=
       originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData;
     ?_)
  have hDomains :
      ((1 / 16 : ℂ) •
        (naturalComp
          pairedOriginalNativePhysicalHilbertChargeColumn.adjoint
          pairedOriginalNativePhysicalHilbertChargeColumn)).domain =
      pairedSU2PhysicalHamiltonian.domain := by
    apply Submodule.ext
    intro u
    simpa only [LinearPMap.smul_domain] using
      (nativeNormalizedSquare_naturalDomain_iff_historical
        theta hCAR hHermitian color gamma J hColor hGamma hJ u)
  apply LinearPMap.ext hDomains
  intro u hs hh
  calc
    ((1 / 16 : ℂ) •
      (naturalComp
        pairedOriginalNativePhysicalHilbertChargeColumn.adjoint
        pairedOriginalNativePhysicalHilbertChargeColumn)) ⟨u,hs⟩ =
        (1 / 16 : ℂ) •
          (naturalComp
            pairedOriginalNativePhysicalHilbertChargeColumn.adjoint
            pairedOriginalNativePhysicalHilbertChargeColumn) ⟨u,hs⟩ := by
      rw [LinearPMap.smul_apply]
    _ = pairedSU2PhysicalHamiltonian ⟨u,hh⟩ :=
      nativeNormalizedSquare_fullAction_eq_historical
        theta hCAR hHermitian color gamma J hColor hGamma hJ u hs hh

#print axioms pairedNativeNormalizedAdjointSquare_eq_historical
end
end FCP.M4F9H4E3D1NativeHistoricalExactPartialOperator
