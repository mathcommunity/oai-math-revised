import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7IndependentActualClosedGraphNamedBridgeE7N1

/-!
M4F7 E7N2 — prospective final independent ACTUAL E2 closed
sixteen-charge operator physical-output theorem.

This leaf combines accepted E7M literal closed-graph physical-output
inclusion with E7N1's exact actual E2 LinearPMap graph equality.
Do not qualify or count this theorem until E7N1 is itself
strictly kernel accepted and E7N2 passes an independent strict
axiom/cache gate.

The genuine original E2 physical-input-cut closed operator is
J-free. The independently defined physical Hilbert space is J-free.
J is an exact source-representation proof witness only.
No domain density, rebased operator, Hamiltonian, or spectrum
claim is made by physical output graph membership alone.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F7IndependentActualClosedPhysicalOutputsE7N2
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

/-- All sixteen output coordinates of EVERY graph point of the
actual independently constructed, minimally CLOSED, physical-
INPUT-cut E2 sixteen-charge partial operator lie in the genuine
independent physical Hilbert submodule, under the original
CAR/Hermitian/source-matching hypotheses. -/
theorem independentPhysicalInputCutClosedChargeColumn_graph_all_outputs_physical
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
        Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) ⊆
      FCP.M4F7IndependentPhysicalOutputPredicateE7I.independentAllSixteenOutputsPhysicalSet
        theta hCAR hHermitian := by
  have hgraph :
      ((FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
        color gamma theta hCAR hHermitian).graph :
          Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) =
        FCP.M4F7OpaqueLiteralGraphInterfaceE7D.literalRestrictedClosedGraphSet
          color gamma theta hCAR hHermitian :=
    FCP.M4F7IndependentActualClosedGraphNamedBridgeE7N1.independentPhysicalInputCutClosedChargeColumn_graph_eq_named_literal
      color gamma theta hCAR hHermitian J hColor hGamma hJ
  exact hgraph.le.trans
    (FCP.M4F7IndependentLiteralClosedPhysicalOutputsE7M.independentLiteralRestrictedClosedGraph_subset_allPhysicalOutputs
      color gamma theta hCAR hHermitian J hColor hGamma hJ)

#print axioms independentPhysicalInputCutClosedChargeColumn_graph_all_outputs_physical

end
end FCP.M4F7IndependentActualClosedPhysicalOutputsE7N2
