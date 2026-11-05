import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7IndependentPhysicalInputCutOperatorE2
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F6IndependentGraphInputCutNamedAlias

/-!
M4F7 E3 — actual source-exact literal restricted smooth graph bridge.

E2 already gives an independent J-free physical-input-cut closed
LinearPMap. M4F6 C2 already identifies the *literal* restricted raw
graph with the native independent full graph satisfying physical input.

This leaf proves a small abstract named-submodule cut membership law,
then composes the accepted exact C2 result and E2 graph theorem.
The enormous BFSS charge formula is NEVER unfolded by tactics.
No new axiom, charge, J-dependent definition or surrogate graph.
Domain density and physical operator/Hamiltonian identification remain open.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F7IndependentLiteralRestrictedGraphBridgeE3
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.IndependentSmoothCore
open FCP.IndependentSmoothSupercharge
open FCP.IndependentPhysicalSpace
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

private abbrev μ := (volume : Measure (Boson 2))

/-- Completely abstract typed native submodule intersection and first
projection. No BFSS definition is present in the proof. -/
private theorem abstract_native_input_cut_mem_iff
    {X Y : Type*}
    [AddCommGroup X] [AddCommGroup Y]
    [Module ℂ X] [Module ℂ Y]
    (G : Submodule ℂ (X × Y)) (P : Submodule ℂ X)
    (p : X × Y) :
    p ∈ (G ⊓ P.comap (LinearMap.fst ℂ X Y)) ↔
      p ∈ G ∧ p.1 ∈ P := by
  change (p ∈ G ∧ (LinearMap.fst ℂ X Y) p ∈ P) ↔
    (p ∈ G ∧ p.1 ∈ P)
  rfl

/-- Exact membership for E2's native, independently constructed
physical input cut, by substituting named independent source objects
into the already proved abstract type-stable interface. -/
theorem independentPhysicalInputCutCoreGraph_mem_iff
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric)
    (p : Lp E 2 μ × (SpinIndex → Lp E 2 μ)) :
    p ∈ FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutCoreGraph
      color gamma theta hCAR hHermitian ↔
    p ∈ independentFullCoreGraph color gamma theta ∧
      p.1 ∈ independentPhysicalSpace theta hCAR hHermitian := by
  unfold FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutCoreGraph
  exact abstract_native_input_cut_mem_iff
    (independentFullCoreGraph color gamma theta)
    (independentPhysicalSpace theta hCAR hHermitian) p

/-- Source-exact equality of the actual independent E2 native smooth
physical graph and the ORIGINAL literal independent restricted range,
using the separately strict-accepted M4F6 C2 theorem. -/
theorem independentPhysicalInputCutCoreGraph_eq_literalRestrictedRange
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    (FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutCoreGraph
      color gamma theta hCAR hHermitian :
        Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) =
    (LinearMap.range
      ((independentCoreToL2.comp
        (independentInvariantCore theta hCAR hHermitian).subtype).prod
        ((independentChargeVector color gamma theta).comp
          (independentInvariantCore theta hCAR hHermitian).subtype)) :
        Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) := by
  apply Set.ext
  intro p
  exact (independentPhysicalInputCutCoreGraph_mem_iff
    color gamma theta hCAR hHermitian p).trans
    ((Set.ext_iff.mp
      (FCP.M4F6IndependentGraphInputCut.independentCoreGraph_eq_physicalInputCut
        color gamma theta hCAR hHermitian) p).symm)

/-- The actual E2 independently defined J-free physical-input-cut
closed sixteen-charge operator has exactly the SET closure of the literal
independent gauge-invariant smooth-core graph. The original physical
Hilbert domain and outputs remain distinct downstream obligations. -/
theorem independentPhysicalInputCutClosedChargeColumn_graph_eq_literal
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
      closure (LinearMap.range
        ((independentCoreToL2.comp
          (independentInvariantCore theta hCAR hHermitian).subtype).prod
          ((independentChargeVector color gamma theta).comp
            (independentInvariantCore theta hCAR hHermitian).subtype)) :
          Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) := by
  rw [FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn_graph_eq
    color gamma theta hCAR hHermitian J hColor hGamma hJ]
  rw [Submodule.topologicalClosure_coe]
  exact congrArg closure
    (independentPhysicalInputCutCoreGraph_eq_literalRestrictedRange
      color gamma theta hCAR hHermitian)

#print axioms independentPhysicalInputCutCoreGraph_mem_iff
#print axioms independentPhysicalInputCutCoreGraph_eq_literalRestrictedRange
#print axioms independentPhysicalInputCutClosedChargeColumn_graph_eq_literal

end
end FCP.M4F7IndependentLiteralRestrictedGraphBridgeE3
