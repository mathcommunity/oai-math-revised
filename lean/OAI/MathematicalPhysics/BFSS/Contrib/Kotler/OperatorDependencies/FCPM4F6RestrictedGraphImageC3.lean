import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F6IndependentGraphInputCutNamedAlias
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F6PairedSourceGraphInputCut

/-!
M4F6 C3 — source-exact restricted independent BFSS 16-charge graph IMAGE.

This file does not import or certify the earlier six-root legacy monolith.
It composes only accepted source exact theorems:
C1 source input cut; C2 literal independent input cut;
M4F4 unrestricted graph image; M4C3 genuine physical-input iff;
and the abstract accepted image_input_cut.

The theorem retains the literal source restricted 17-component graph and
the independently defined J-free restricted 17-component graph. No new
graph definition, transported physical-space definition or premise occurs.
This is a candidate; acceptance requires a separate strict gate.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.M4F6RestrictedGraphImageC3
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentSmoothCore
open FCP.IndependentSmoothSupercharge
open FCP.IndependentFullL2GaugeTransport
open FCP.IndependentPhysicalSpace
open FCP.RestrictedGraphInputCut
open MeasureTheory
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))

/-- Genuine original BFSS physical-input restricted smooth graph equals
the 17-component fiber image of the literal independently specified
physical-input restricted smooth graph. The conclusion does not assert
the sixteen outputs are physical, the graph is closable, or any Hamiltonian
or spectral equality. -/
theorem sourceRestrictedCoreGraph_eq_independent_image
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hColor : color = pairedAlgebraData.color)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w)) :
    (LinearMap.range
      ((coreToL2.comp pairedGaugeData.invariantCore.subtype).prod
        (pairedAlgebraData.chargeVector.comp
          pairedGaugeData.invariantCore.subtype)) :
      Set (FullL2 2 × (SpinIndex → FullL2 2))) =
    (independentGraphTransportHomeomorph J) ''
      (LinearMap.range
        ((independentCoreToL2.comp
          (independentInvariantCore theta hCAR hHermitian).subtype).prod
          ((independentChargeVector color gamma theta).comp
            (independentInvariantCore theta hCAR hHermitian).subtype)) :
        Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) := by
  have hPhysical
      (p : Lp E 2 μ × (SpinIndex → Lp E 2 μ)) :
      p.1 ∈ independentPhysicalSpace theta hCAR hHermitian ↔
      (independentGraphTransportHomeomorph J p).1 ∈
        pairedGaugeData.physicalSpace := by
    exact independentPhysicalSpace_iff_source theta hCAR hHermitian J hJ p.1
  have hFull :
      (pairedAlgebraData.fullCoreGraph :
        Set (FullL2 2 × (SpinIndex → FullL2 2))) =
      (independentGraphTransportHomeomorph J) ''
        (independentFullCoreGraph color gamma theta :
          Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) :=
    sourceFullCoreGraph_eq_independent_image
      color gamma theta J hColor hGamma hJ
  calc
    (LinearMap.range
      ((coreToL2.comp pairedGaugeData.invariantCore.subtype).prod
        (pairedAlgebraData.chargeVector.comp
          pairedGaugeData.invariantCore.subtype)) :
      Set (FullL2 2 × (SpinIndex → FullL2 2))) =
        {q | q ∈ pairedAlgebraData.fullCoreGraph ∧
          q.1 ∈ pairedGaugeData.physicalSpace} :=
      FCP.M4F6PairedSourceGraphInputCut.pairedSourceCoreGraph_eq_physicalInputCut
    _ = (independentGraphTransportHomeomorph J) ''
      {p | p ∈ independentFullCoreGraph color gamma theta ∧
        p.1 ∈ independentPhysicalSpace theta hCAR hHermitian} :=
      image_input_cut
        (independentGraphTransportHomeomorph J)
        (independentFullCoreGraph color gamma theta : Set _)
        (pairedAlgebraData.fullCoreGraph : Set _)
        (fun p => p.1 ∈ independentPhysicalSpace theta hCAR hHermitian)
        (fun q => q.1 ∈ pairedGaugeData.physicalSpace)
        hFull hPhysical
    _ = (independentGraphTransportHomeomorph J) ''
      (LinearMap.range
        ((independentCoreToL2.comp
          (independentInvariantCore theta hCAR hHermitian).subtype).prod
          ((independentChargeVector color gamma theta).comp
            (independentInvariantCore theta hCAR hHermitian).subtype)) :
        Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) :=
      congrArg
        (fun S : Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ)) =>
          (independentGraphTransportHomeomorph J) '' S)
        (FCP.M4F6IndependentGraphInputCut.independentCoreGraph_eq_physicalInputCut
          color gamma theta hCAR hHermitian).symm

#print axioms sourceRestrictedCoreGraph_eq_independent_image
#check sourceRestrictedCoreGraph_eq_independent_image

end
end FCP.M4F6RestrictedGraphImageC3
