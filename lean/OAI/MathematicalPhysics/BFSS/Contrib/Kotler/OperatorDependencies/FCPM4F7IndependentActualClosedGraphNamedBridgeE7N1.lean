import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7IndependentLiteralClosedPhysicalOutputsE7M
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7IndependentLiteralRestrictedGraphBridgeE3

/-!
BFSS SU(2) M4F7 E7N1 — Exact real E2 closed partial operator
graph equals accepted E7D J-free independent literal closed graph.

This is an *equality* certificate, not a new graph, operator or
physical Hilbert space. It composes two strictly accepted original
kernel proofs, E3 (E2 graph = closure of literal product range)
and E7D (that same closure = exact independently named set).

No charge formulas are unfolded. J remains an external source
representation witness, never part of the E2/E7D definitions.
This supporting identity is to be compiled before the final E7N2
true E2-graph physical-output theorem. Neither equality alone
asserts dense domain, physical rebasing, Hamiltonian or spectrum.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F7IndependentActualClosedGraphNamedBridgeE7N1
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentSmoothCore
open FCP.IndependentSmoothSupercharge
open FCP.IndependentPhysicalSpace
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))

/-- The graph of the ACTUAL native E2 J-free independent physical-input
closed partial charge operator is exactly E7D's originally defined
literal gauge-invariant closed smooth-core graph. -/
theorem independentPhysicalInputCutClosedChargeColumn_graph_eq_named_literal
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
    ((FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
      color gamma theta hCAR hHermitian).graph :
        Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) =
      FCP.M4F7OpaqueLiteralGraphInterfaceE7D.literalRestrictedClosedGraphSet
        color gamma theta hCAR hHermitian := by
  exact (FCP.M4F7IndependentLiteralRestrictedGraphBridgeE3.independentPhysicalInputCutClosedChargeColumn_graph_eq_literal
    color gamma theta hCAR hHermitian J hColor hGamma hJ).trans
      (FCP.M4F7OpaqueLiteralGraphInterfaceE7D.literalRestrictedClosedGraphSet_eq
        color gamma theta hCAR hHermitian).symm

#print axioms independentPhysicalInputCutClosedChargeColumn_graph_eq_named_literal

end
end FCP.M4F7IndependentActualClosedGraphNamedBridgeE7N1
