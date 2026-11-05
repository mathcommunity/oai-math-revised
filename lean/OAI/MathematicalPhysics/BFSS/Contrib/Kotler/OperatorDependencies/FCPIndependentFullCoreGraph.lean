import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentChargeVectorL2

/-!
M4F3 — independently defined *unrestricted* smooth-core joint-charge
graph and its precise image in the pinned original source fullCoreGraph.

This deliberately precedes gauge restriction and operator closure.
The graph is defined J-free using the actual independent L² core
embedding and sixteen independent charge components. No physical
core density, gauge covariance or spectral statement is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.IndependentSmoothSupercharge
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.IndependentSmoothCore
open FCP.IndependentFullL2GaugeTransport
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

private abbrev μ := (volume : Measure (Boson 2))

/-- True J-free graph of the independently defined full smooth-core
charge column, inside the independent L² field-plus-output product. -/
def independentFullCoreGraph
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E) :
    Submodule ℂ (Lp E 2 μ × (SpinIndex → Lp E 2 μ)) :=
  LinearMap.range
    (independentCoreToL2.prod (independentChargeVector color gamma theta))

/-- The accepted pointwise source intertwiner applies simultaneously
to the complete finite sixteen-charge column. -/
theorem independentChargeVector_all_components_intertwining
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hColor : color = pairedAlgebraData.color)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (f : IndependentTestCore E) :
    (fun α : SpinIndex =>
      fiberTransport J (independentChargeVector color gamma theta f α)) =
      pairedAlgebraData.chargeVector (independentSmoothTransport J f) := by
  funext α
  exact independentChargeVector_component_intertwining
    color gamma theta J hColor hGamma hJ α f

/-- EVERY element of the genuinely independent unrestricted smooth
charge graph transports into the literal original source fullCoreGraph.
Surjectivity, equality of closed graphs and gauge restriction are NOT
asserted here. -/
theorem independentFullCoreGraph_transport_mem_source
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hColor : color = pairedAlgebraData.color)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (p : Lp E 2 μ × (SpinIndex → Lp E 2 μ))
    (hp : p ∈ independentFullCoreGraph color gamma theta) :
    (fiberTransport J p.1,
      fun α : SpinIndex => fiberTransport J (p.2 α)) ∈
      pairedAlgebraData.fullCoreGraph := by
  rcases hp with ⟨f, rfl⟩
  change (fiberTransport J (independentCoreToL2 f),
      fun α : SpinIndex =>
        fiberTransport J (independentChargeVector color gamma theta f α)) ∈
    pairedAlgebraData.fullCoreGraph
  change ∃ g : SmoothCore 2,
      (coreToL2.prod pairedAlgebraData.chargeVector) g =
        (fiberTransport J (independentCoreToL2 f),
          fun α : SpinIndex =>
            fiberTransport J (independentChargeVector color gamma theta f α))
  refine ⟨independentSmoothTransport J f, ?_⟩
  apply Prod.ext
  · exact (independentSmoothTransport_coreToL2 J f).symm
  · exact (independentChargeVector_all_components_intertwining
      color gamma theta J hColor hGamma hJ f).symm

#print axioms independentFullCoreGraph
#print axioms independentChargeVector_all_components_intertwining
#print axioms independentFullCoreGraph_transport_mem_source

end
end FCP.IndependentSmoothSupercharge
