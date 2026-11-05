import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4C1ANamedSourceAmbientIndependentInputWitness
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H2D1ActualE2HilbertOutputDomainEquivalence

/-!
BFSS M4F9 H4C1B — native Hilbert input-domain recovery from the ACTUAL
original AY source physical charge, using a qualified H4C1A source
named-graph independent full physical input witness and H2D1's exact
natural independent E2 Hilbert domain iff.

This is one direction of domain identification only; no graph output
equality or source-defined replacement for independent J-free charge.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H4C1BSourceDomainIndependentNativeRecovery
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open FCP.M4F9H2CActualE2NativeHilbertChargeColumn
open FCP.M4F9H3B1OriginalAYNativePhysicalHilbertGraphRebase
open FCP.M4F9H3B2OriginalAYNativePhysicalHilbertChargeColumn
open FCP.M4F9H4B1ASourceNamedNativeGraphMembership
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

/-- Every ACTUAL original source native charge input pulls back under
the physical input unitary to the full natural domain of the genuinely
independent E2 native physical Hilbert charge. -/
theorem nativeSourceDomain_symm_mem_independentDomain
    (x : pairedGaugeData.physicalSpace)
    (hx : x ∈ pairedOriginalNativePhysicalHilbertChargeColumn.domain) :
    (independentPhysicalUnitary theta hCAR hHermitian J hJ).symm x ∈
      (independentActualE2NativeHilbertChargeColumn
        theta hCAR hHermitian color gamma).domain := by
  obtain ⟨v, hv⟩ := (LinearPMap.mem_domain_iff).mp hx
  have hphys : (x,v) ∈ pairedOriginalPhysicalHilbertChargeGraph := by
    rwa [pairedOriginalNativePhysicalHilbertChargeColumn_graph_eq] at hv
  have hnamed :
      ((x : FullL2 2),
        fun α : SpinIndex =>
          ((v α : pairedGaugeData.physicalSpace) : FullL2 2)) ∈
      (pairedGaugeData.deformedModelGraph 1 0 :
        Set (FullL2 2 × (SpinIndex → FullL2 2))) :=
    (pairedNativeSourcePhysicalGraph_mem_source_iff (x,v)).mp hphys
  obtain ⟨q, hq, hqinput⟩ :=
    FCP.M4F9H4C1ANamedSourceAmbientIndependentInputWitness.namedSourceGraph_independentFullPhysicalInput_exists
      theta hCAR hHermitian color gamma J hColor hGamma hJ x _ hnamed
  have hfull : q.1 ∈
      (FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn
        color gamma theta hCAR hHermitian).domain :=
    (LinearPMap.mem_domain_iff).mpr ⟨q.2, hq⟩
  have hnative : q.1 ∈
      (independentActualE2NativeHilbertChargeColumn
        theta hCAR hHermitian color gamma).domain :=
    (FCP.M4F9H2D1ActualE2HilbertOutputDomainEquivalence.independentActualE2NativeHilbertChargeColumn_domain_iff
      theta hCAR hHermitian color gamma q.1).mpr hfull
  have hpre :
      (independentPhysicalUnitary theta hCAR hHermitian J hJ).symm x = q.1 := by
    rw [← hqinput]
    exact (independentPhysicalUnitary theta hCAR hHermitian J hJ).symm_apply_apply q.1
  rw [hpre]
  exact hnative

#print axioms nativeSourceDomain_symm_mem_independentDomain
end
end FCP.M4F9H4C1BSourceDomainIndependentNativeRecovery
