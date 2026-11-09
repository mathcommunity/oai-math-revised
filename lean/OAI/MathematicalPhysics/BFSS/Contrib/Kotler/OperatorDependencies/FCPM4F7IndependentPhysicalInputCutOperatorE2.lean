import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7IndependentFullClosedChargeOperatorE1
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentPhysicalSpace

/-!
M4F7 E2 — a J-free physically input-cut independent charge relation and
its genuine minimal closed LinearPMap, built by intersecting the actual
named unrestricted independent smooth-core graph with the INDEPENDENT
physical input constraint.

E1/B4 furnish unrestricted vertical uniqueness; native submodule
monotonicity transfers it without unfolding BFSS charge formulas.
This deliberately does not claim the still-unqualified concrete
equality to the old literal restricted-range graph presentation.
No density, all-physical output, Hamiltonian or spectrum claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F7IndependentPhysicalInputCutOperatorE2
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.IndependentSmoothSupercharge
open FCP.IndependentPhysicalSpace
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

private abbrev μ := (volume : Measure (Boson 2))

/-- The original, J-free independent FULL smooth-core charge graph
cut to physical INPUTS using the independently defined native SU(2)
constraint. This is NOT defined by transporting a source graph. -/
noncomputable def independentPhysicalInputCutCoreGraph
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    Submodule ℂ (Lp E 2 μ × (SpinIndex → Lp E 2 μ)) :=
  independentFullCoreGraph color gamma theta ⊓
    (independentPhysicalSpace theta hCAR hHermitian).comap
      (LinearMap.fst ℂ (Lp E 2 μ) (SpinIndex → Lp E 2 μ))

/-- Restricting the actual independent named full smooth graph to its
native physical input condition can only remove graph points. -/
theorem independentPhysicalInputCutCoreGraph_le_full
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    independentPhysicalInputCutCoreGraph color gamma theta hCAR hHermitian ≤
      independentFullCoreGraph color gamma theta := by
  unfold independentPhysicalInputCutCoreGraph
  exact inf_le_left

/-- Actual J-free physically input-cut minimal independent 16-charge
partial operator, formed from the native closure of the independent graph
with independently imposed physical input constraints. -/
noncomputable def independentPhysicalInputCutClosedChargeColumn
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    Lp E 2 μ →ₗ.[ℂ] (SpinIndex → Lp E 2 μ) :=
  (independentPhysicalInputCutCoreGraph
    color gamma theta hCAR hHermitian).topologicalClosure.toLinearPMap

/-- Native graph identity of the genuinely independent physically input-cut
operator. J appears only as a proof witness, never in either definition. -/
theorem independentPhysicalInputCutClosedChargeColumn_graph_eq
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
    (independentPhysicalInputCutClosedChargeColumn
      color gamma theta hCAR hHermitian).graph =
        (independentPhysicalInputCutCoreGraph
          color gamma theta hCAR hHermitian).topologicalClosure := by
  unfold independentPhysicalInputCutClosedChargeColumn
  apply FCP.M4F7GenericOpaqueClosedRelationBridge.topologicalClosure_toLinearPMap_graph_eq
  rintro ⟨x, y⟩ hp hx
  dsimp at hx
  subst x
  have hcut : ((0 : Lp E 2 μ), y) ∈
      (independentPhysicalInputCutCoreGraph
        color gamma theta hCAR hHermitian).topologicalClosure := by
    rw [← Submodule.topologicalClosure_coe
      (independentPhysicalInputCutCoreGraph
        color gamma theta hCAR hHermitian)] at hp
    exact hp
  have hfull : ((0 : Lp E 2 μ), y) ∈
      (independentFullCoreGraph color gamma theta).topologicalClosure :=
    (Submodule.topologicalClosure_mono
      (independentPhysicalInputCutCoreGraph_le_full
        color gamma theta hCAR hHermitian)) hcut
  apply FCP.M4F7FullClosedGraphVerticalB4.independentFullCoreGraph_closure_vertical
    color gamma theta J hColor hGamma hJ y
  rw [← Submodule.topologicalClosure_coe (independentFullCoreGraph color gamma theta)]
  exact hfull

/-- The new physically input-cut independent partial operator is closed
as an ambient-Lp-input operator; no density or physical output is inferred. -/
theorem independentPhysicalInputCutClosedChargeColumn_isClosed
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
    (independentPhysicalInputCutClosedChargeColumn
      color gamma theta hCAR hHermitian).IsClosed := by
  change IsClosed ((independentPhysicalInputCutClosedChargeColumn
      color gamma theta hCAR hHermitian).graph :
    Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ)))
  rw [independentPhysicalInputCutClosedChargeColumn_graph_eq
    color gamma theta hCAR hHermitian J hColor hGamma hJ]
  exact Submodule.isClosed_topologicalClosure _

/-- The closed physical-input-cut independent graph is contained in the
genuine unrestricted E1 independent closed operator graph. This is NOT
an equality and does not identify the literal raw physical graph alias. -/
theorem independentPhysicalInputCutClosedChargeColumn_graph_le_full
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
    (independentPhysicalInputCutClosedChargeColumn
      color gamma theta hCAR hHermitian).graph ≤
      (FCP.M4F7IndependentFullClosedChargeOperatorE1.independentFullClosedChargeColumn
        color gamma theta).graph := by
  rw [independentPhysicalInputCutClosedChargeColumn_graph_eq
    color gamma theta hCAR hHermitian J hColor hGamma hJ,
    FCP.M4F7IndependentFullClosedChargeOperatorE1.independentFullClosedChargeColumn_graph_eq
      color gamma theta J hColor hGamma hJ]
  exact Submodule.topologicalClosure_mono
    (independentPhysicalInputCutCoreGraph_le_full color gamma theta hCAR hHermitian)

#print axioms independentPhysicalInputCutCoreGraph
#print axioms independentPhysicalInputCutCoreGraph_le_full
#print axioms independentPhysicalInputCutClosedChargeColumn
#print axioms independentPhysicalInputCutClosedChargeColumn_graph_eq
#print axioms independentPhysicalInputCutClosedChargeColumn_isClosed
#print axioms independentPhysicalInputCutClosedChargeColumn_graph_le_full

end
end FCP.M4F7IndependentPhysicalInputCutOperatorE2
