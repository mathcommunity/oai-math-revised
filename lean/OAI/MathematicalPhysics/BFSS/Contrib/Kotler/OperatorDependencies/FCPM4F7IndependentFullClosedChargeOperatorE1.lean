import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7FullClosedGraphVerticalB4CoeAlign
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7GenericOpaqueClosedRelationBridgeImports

/-!
M4F7 E1 — genuinely independent J-free UNRESTRICTED closed 16-charge
partial operator. Uses the strictly accepted source-exact named B4
vertical theorem and the independently accepted abstract B2 certificates.

This is deliberately NOT the physically restricted M4F7 D1 operator.
It does NOT settle the restricted physical core, domain density, physical
output, source operator/domain equivalence, Hamiltonian or spectrum.
No new assumption, axiom, surrogate charge, or source-transported
operator is introduced into the definition.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F7IndependentFullClosedChargeOperatorE1
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.IndependentSmoothSupercharge
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

private abbrev μ := (volume : Measure (Boson 2))

/-- J-free minimal partial charge column from the actual unrestricted
independent smooth-core sixteen-charge graph, not a transported source
operator. The graph equality needs a separate exact representation witness. -/
noncomputable def independentFullClosedChargeColumn
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E) :
    Lp E 2 μ →ₗ.[ℂ] (SpinIndex → Lp E 2 μ) :=
  (independentFullCoreGraph color gamma theta).topologicalClosure.toLinearPMap

/-- The actual J-free independent unrestricted minimal charge column has
precisely the native topological closure of its genuine smooth-core graph,
provided the exact original/source representation-identification hypotheses. -/
theorem independentFullClosedChargeColumn_graph_eq
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hColor : color = pairedAlgebraData.color)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w)) :
    (independentFullClosedChargeColumn color gamma theta).graph =
      (independentFullCoreGraph color gamma theta).topologicalClosure := by
  unfold independentFullClosedChargeColumn
  apply FCP.M4F7GenericOpaqueClosedRelationBridge.topologicalClosure_toLinearPMap_graph_eq
  rintro ⟨x, y⟩ hp hx
  dsimp at hx
  subst x
  exact FCP.M4F7FullClosedGraphVerticalB4.independentFullCoreGraph_closure_vertical
    color gamma theta J hColor hGamma hJ y hp

/-- Genuine closedness of the independently defined unrestricted charge
column, derived from the qualified graph equality, not a generic assertion
that all linear relations define single-valued closed operators. -/
theorem independentFullClosedChargeColumn_isClosed
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hColor : color = pairedAlgebraData.color)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w)) :
    (independentFullClosedChargeColumn color gamma theta).IsClosed := by
  change IsClosed ((independentFullClosedChargeColumn color gamma theta).graph :
    Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ)))
  rw [independentFullClosedChargeColumn_graph_eq
    color gamma theta J hColor hGamma hJ]
  exact Submodule.isClosed_topologicalClosure _

#print axioms independentFullClosedChargeColumn
#print axioms independentFullClosedChargeColumn_graph_eq
#print axioms independentFullClosedChargeColumn_isClosed
#check independentFullClosedChargeColumn_graph_eq

end
end FCP.M4F7IndependentFullClosedChargeOperatorE1
