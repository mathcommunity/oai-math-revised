import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F6RestrictedGraphImageC3

/-!
M4F6 C4 — CONTINGENT strict-candidate source-exact restricted graph CLOSURE.

This file depends on the separately accepted strict C3 restricted
graph-image theorem. Its own C4 closure result remains a candidate
and requires a separate source-pinned kernel and axiom gate.

The result concerns closure of the literal BFSS smooth-core joint
sixteen-charge GRAPH RELATION under the 17-slot fiber homeomorphism.
It does NOT establish graph single-valuedness, closability, equality of
closed unbounded operators, Hamiltonian domains, or spectrum.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F6RestrictedGraphClosureC4
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentSmoothCore
open FCP.IndependentSmoothSupercharge
open FCP.IndependentFullL2GaugeTransport
open FCP.IndependentPhysicalSpace
open MeasureTheory
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))

/-- Exact closure of the genuinely source-defined gauge-restricted
sixteen-charge graph relation equals the fiberwise transport of the
closure of the genuinely independent restricted smooth-core graph. -/
theorem sourceRestrictedCoreGraph_closure_eq_independent_image_closure
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
    closure (LinearMap.range
      ((coreToL2.comp pairedGaugeData.invariantCore.subtype).prod
        (pairedAlgebraData.chargeVector.comp
          pairedGaugeData.invariantCore.subtype)) :
      Set (FullL2 2 × (SpinIndex → FullL2 2))) =
    (independentGraphTransportHomeomorph J) ''
      closure (LinearMap.range
        ((independentCoreToL2.comp
          (independentInvariantCore theta hCAR hHermitian).subtype).prod
          ((independentChargeVector color gamma theta).comp
            (independentInvariantCore theta hCAR hHermitian).subtype)) :
        Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) := by
  calc
    closure (LinearMap.range
      ((coreToL2.comp pairedGaugeData.invariantCore.subtype).prod
        (pairedAlgebraData.chargeVector.comp
          pairedGaugeData.invariantCore.subtype)) :
      Set (FullL2 2 × (SpinIndex → FullL2 2))) =
      closure ((independentGraphTransportHomeomorph J) ''
        (LinearMap.range
          ((independentCoreToL2.comp
            (independentInvariantCore theta hCAR hHermitian).subtype).prod
            ((independentChargeVector color gamma theta).comp
              (independentInvariantCore theta hCAR hHermitian).subtype)) :
          Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ)))) := by
        exact congrArg closure
          (FCP.M4F6RestrictedGraphImageC3.sourceRestrictedCoreGraph_eq_independent_image
            color gamma theta hCAR hHermitian J hColor hGamma hJ)
    _ = (independentGraphTransportHomeomorph J) ''
      closure (LinearMap.range
        ((independentCoreToL2.comp
          (independentInvariantCore theta hCAR hHermitian).subtype).prod
          ((independentChargeVector color gamma theta).comp
            (independentInvariantCore theta hCAR hHermitian).subtype)) :
        Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) := by
          exact ((independentGraphTransportHomeomorph J).image_closure
            (LinearMap.range
              ((independentCoreToL2.comp
                (independentInvariantCore theta hCAR hHermitian).subtype).prod
                ((independentChargeVector color gamma theta).comp
                  (independentInvariantCore theta hCAR hHermitian).subtype)) :
              Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ)))).symm

#print axioms sourceRestrictedCoreGraph_closure_eq_independent_image_closure
#check sourceRestrictedCoreGraph_closure_eq_independent_image_closure

end
end FCP.M4F6RestrictedGraphClosureC4
