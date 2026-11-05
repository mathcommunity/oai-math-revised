import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentFullCoreGraphClosure

/-!
M4F7 B4 research candidate — exact unrestricted independent BFSS
sixteen-charge closed graph has trivial vertical fiber.

Unlike failed A2 set-alias attempts, the transport argument uses the
already NAMED independentFullCoreGraph and original fullCoreGraph,
plus the strictly accepted M4F5 17-slot closure transport equality.
This is not proof of the physically restricted closed LinearPMap.
Gate #2 modifies only the orientation and target of the single
source closure-coercion rewrite that failed at B4 Gate #1.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.M4F7FullClosedGraphVerticalB4
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.IndependentSmoothCore
open FCP.IndependentSmoothSupercharge
open FCP.IndependentFullL2GaugeTransport
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

private abbrev μ := (volume : Measure (Boson 2))

/-- The genuine independent UNRESTRICTED closed joint-charge graph
has trivial vertical fiber under the actual original-source representation
identification witnesses. This is a closed relation, not yet a physical
operator equivalence. -/
theorem independentFullCoreGraph_closure_vertical
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hColor : color = pairedAlgebraData.color)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (y : SpinIndex → Lp E 2 μ)
    (hy : ((0 : Lp E 2 μ), y) ∈
      closure (independentFullCoreGraph color gamma theta :
        Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ)))) :
    y = 0 := by
  let H := independentGraphTransportHomeomorph J
  have hsrc : H ((0 : Lp E 2 μ), y) ∈
      closure (pairedAlgebraData.fullCoreGraph :
        Set (FullL2 2 × (SpinIndex → FullL2 2))) := by
    rw [sourceFullCoreGraph_closure_eq_independent_image_closure
      color gamma theta J hColor hGamma hJ]
    exact ⟨((0 : Lp E 2 μ), y), hy, rfl⟩
  have hsourceZero :
      ((0 : FullL2 2), fun α : SpinIndex => fiberTransport J (y α)) ∈
      pairedAlgebraData.fullClosedGraph := by
    have hh := hsrc
    change (fiberTransport J (0 : Lp E 2 μ),
      fun α : SpinIndex => fiberTransport J (y α)) ∈
        closure (pairedAlgebraData.fullCoreGraph :
          Set (FullL2 2 × (SpinIndex → FullL2 2))) at hh
    have hh0 :
        ((0 : FullL2 2), fun α : SpinIndex => fiberTransport J (y α)) ∈
          closure (pairedAlgebraData.fullCoreGraph :
            Set (FullL2 2 × (SpinIndex → FullL2 2))) := by
      simpa only [(fiberTransport J).map_zero] using hh
    change ((0 : FullL2 2), fun α : SpinIndex => fiberTransport J (y α)) ∈
      pairedAlgebraData.fullCoreGraph.topologicalClosure
    rw [← Submodule.topologicalClosure_coe pairedAlgebraData.fullCoreGraph] at hh0
    exact hh0
  have hzero : (fun α : SpinIndex => fiberTransport J (y α)) = 0 :=
    pairedAlgebraData.fullClosedGraph_vertical hsourceZero
  funext α
  apply (fiberTransportUnitary J).injective
  change fiberTransport J (y α) = fiberTransport J (0 : Lp E 2 μ)
  have hα : fiberTransport J (y α) = 0 := by
    simpa only [Pi.zero_apply] using congrFun hzero α
  simpa only [(fiberTransport J).map_zero] using hα

#print axioms independentFullCoreGraph_closure_vertical
#check independentFullCoreGraph_closure_vertical

end
end FCP.M4F7FullClosedGraphVerticalB4
