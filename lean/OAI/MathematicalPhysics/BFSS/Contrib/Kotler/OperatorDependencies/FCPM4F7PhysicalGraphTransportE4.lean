import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7IndependentLiteralRestrictedGraphBridgeE3
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F6RestrictedGraphClosureC4

/-!
M4F7 E4 — exact source/independent transport of the genuine independent
J-free physically input-cut minimally closed 16-supercharge operator graph.

C4 already establishes the source-restricted smooth-core graph CLOSURE
as the 17-slot fiber homeomorphism image of the literal independent
restricted smooth-core graph closure. E3 identifies that literal
independent closure with the actual E2 closed partial operator graph.

This is an actual theorem about the E2 LinearPMap graph and the
literal original-source smooth-core GRAPH CLOSURE.
It does not silently identify the source closure with the original
deformedModelGraph operator or infer any physical domain density,
physical output membership, Hamiltonian, Spin(9) or spectrum.

E2's mathematical operator definition remains J-free. J appears
solely as the strict source/independent representation witness.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F7PhysicalGraphTransportE4
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentSmoothCore
open FCP.IndependentSmoothSupercharge
open FCP.IndependentFullL2GaugeTransport
open FCP.IndependentPhysicalSpace
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))

/-- Exact source-restricted original 16-supercharge smooth-core graph
CLOSURE is precisely the 17-component fiber homeomorphism image of
the actual independently specified J-free E2 CLOSED operator graph.
No transported *definition* or fictitious source graph is used. -/
theorem sourceRestrictedCoreClosure_eq_independentPhysicalOperatorGraph_image
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
      ((FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
        color gamma theta hCAR hHermitian).graph :
          Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) := by
  calc
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
            Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) :=
      FCP.M4F6RestrictedGraphClosureC4.sourceRestrictedCoreGraph_closure_eq_independent_image_closure
        color gamma theta hCAR hHermitian J hColor hGamma hJ
    _ = (independentGraphTransportHomeomorph J) ''
      ((FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
        color gamma theta hCAR hHermitian).graph :
          Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) :=
      congrArg
        (fun S : Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ)) =>
          (independentGraphTransportHomeomorph J) '' S)
        (FCP.M4F7IndependentLiteralRestrictedGraphBridgeE3.independentPhysicalInputCutClosedChargeColumn_graph_eq_literal
          color gamma theta hCAR hHermitian J hColor hGamma hJ).symm

#print axioms sourceRestrictedCoreClosure_eq_independentPhysicalOperatorGraph_image
#check sourceRestrictedCoreClosure_eq_independentPhysicalOperatorGraph_image

end
end FCP.M4F7PhysicalGraphTransportE4
