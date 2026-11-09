import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F8IndependentActualE2FullPhysicalDomainDE2B
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7PhysicalGraphTransportE4

/-!
BFSS M4F8 DE3 — prospective source-exact graph transport of the genuine
J-free, closed, densely defined physical-to-physical E2 charge.
E6 makes the actual ambient graph input physical, E7N2 makes all 16
outputs physical, and DE2 identifies their exact subtype graph.
E4 transports the ambient graph to the original restricted smooth-core
closure. This DOES NOT identify that closure with named deformedModelGraph
1 0: its historical D1 import is not yet qualified on this branch.
Candidate only; no root accepted before a strict gate.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F8IndependentActualPhysicalGraphSourceTransportDE3
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open FCP.IndependentSmoothSupercharge
open FCP.IndependentFullL2GaugeTransport
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))

variable (color : ColorIndex 2 → ColorMatrix 2)
  (gamma : SpaceIndex → GammaMatrix)
  (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
  (hCAR : ∀ α β A B,
    theta α A * theta β B + theta β B * theta α A =
      (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
  (hHermitian : ∀ α A, (theta α A).IsSymmetric)
  (J : E ≃ₗᵢ[ℂ] Fermion 2)
  (hColor : color = pairedAlgebraData.color)
  (hGamma : gamma = pairedAlgebraData.gamma)
  (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))

-- These proof witnesses do not occur in the first theorem proposition.
-- Force them into both theorem contexts; do not alter graph statements.
include J hColor hGamma hJ

/-- Exact graph of E2, not an extension, is the physical graph image
through both its original, independently defined subtype inclusions. -/
theorem actualE2AmbientGraph_eq_fullPhysicalGraph_image :
    ((FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
      color gamma theta hCAR hHermitian).graph :
        Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) =
    (fun p : independentPhysicalSpace theta hCAR hHermitian ×
      FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualPhysicalOutputs
        theta hCAR hHermitian =>
      ((p.1 : Lp E 2 μ), (p.2 : SpinIndex → Lp E 2 μ))) ''
      ((FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn
        color gamma theta hCAR hHermitian).graph : Set _) := by
  apply Set.ext
  rintro ⟨x, y⟩
  constructor
  · intro hxy
    have hx : x ∈ independentPhysicalSpace theta hCAR hHermitian :=
      FCP.M4F7IndependentClosedChargePhysicalInputE6.independentPhysicalInputCutClosedChargeColumn_input_physical
        color gamma theta hCAR hHermitian J hColor hGamma hJ (x, y) hxy
    have hall : ∀ α : SpinIndex, y α ∈
        independentPhysicalSpace theta hCAR hHermitian :=
      (FCP.M4F7IndependentPhysicalOutputPredicateE7I.mem_independentAllSixteenOutputsPhysicalSet_iff
        theta hCAR hHermitian (x, y)).mp
        (FCP.M4F7IndependentActualClosedPhysicalOutputsE7N2.independentPhysicalInputCutClosedChargeColumn_graph_all_outputs_physical
          color gamma theta hCAR hHermitian J hColor hGamma hJ hxy)
    have hy : y ∈
        FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualPhysicalOutputs
          theta hCAR hHermitian := by
      change y ∈ Submodule.pi Set.univ
        (fun (_ : SpinIndex) => independentPhysicalSpace theta hCAR hHermitian)
      exact (Submodule.mem_pi).mpr (fun α _ => hall α)
    refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), ?_, rfl⟩
    rw [FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn_graph_eq]
    exact (FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalGraph_mem_iff
      color gamma theta hCAR hHermitian _).mpr hxy
  · rintro ⟨p, hp, hpair⟩
    rw [← hpair]
    apply (FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalGraph_mem_iff
      color gamma theta hCAR hHermitian p).mp
    rw [← FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn_graph_eq]
    exact hp

/-- The ORIGINAL restricted source smooth-core closure is literally
the 17-slot fiber image of the true independently defined physical
charge graph. This is not yet the named deformedModelGraph equality. -/
theorem sourceRestrictedClosure_eq_actualFullPhysicalE2Graph_image :
    closure (LinearMap.range
      ((coreToL2.comp pairedGaugeData.invariantCore.subtype).prod
        (pairedAlgebraData.chargeVector.comp
          pairedGaugeData.invariantCore.subtype)) :
        Set (FullL2 2 × (SpinIndex → FullL2 2))) =
    (independentGraphTransportHomeomorph J) ''
      ((fun p : independentPhysicalSpace theta hCAR hHermitian ×
        FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualPhysicalOutputs
          theta hCAR hHermitian =>
        ((p.1 : Lp E 2 μ), (p.2 : SpinIndex → Lp E 2 μ))) ''
        ((FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn
          color gamma theta hCAR hHermitian).graph : Set _)) := by
  calc
    closure (LinearMap.range
      ((coreToL2.comp pairedGaugeData.invariantCore.subtype).prod
        (pairedAlgebraData.chargeVector.comp
          pairedGaugeData.invariantCore.subtype)) :
        Set (FullL2 2 × (SpinIndex → FullL2 2))) =
      (independentGraphTransportHomeomorph J) ''
        ((FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
          color gamma theta hCAR hHermitian).graph :
            Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) :=
      FCP.M4F7PhysicalGraphTransportE4.sourceRestrictedCoreClosure_eq_independentPhysicalOperatorGraph_image
        color gamma theta hCAR hHermitian J hColor hGamma hJ
    _ = (independentGraphTransportHomeomorph J) ''
      ((fun p : independentPhysicalSpace theta hCAR hHermitian ×
        FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualPhysicalOutputs
          theta hCAR hHermitian =>
        ((p.1 : Lp E 2 μ), (p.2 : SpinIndex → Lp E 2 μ))) ''
        ((FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn
          color gamma theta hCAR hHermitian).graph : Set _)) :=
      congrArg
        (fun S : Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ)) =>
          (independentGraphTransportHomeomorph J) '' S)
        (actualE2AmbientGraph_eq_fullPhysicalGraph_image
          color gamma theta hCAR hHermitian J hColor hGamma hJ)

#print axioms actualE2AmbientGraph_eq_fullPhysicalGraph_image
#print axioms sourceRestrictedClosure_eq_actualFullPhysicalE2Graph_image
end
end FCP.M4F8IndependentActualPhysicalGraphSourceTransportDE3
