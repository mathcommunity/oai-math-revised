import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentGraphTransportHomeomorph

/-!
M4F5B — closure of the actual original BFSS source unrestricted
smooth-core sixteen-charge graph equals the 17-component unitary fiber
transport of the closure of the genuine independent smooth-core graph.

This is a topological closed SUBSET / closed RELATION statement.
It does not prove single-valued operator closability, gauge-invariant
physical charge domains, Hamiltonian equality or spectrum.
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
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

private abbrev μ := (volume : Measure (Boson 2))

/-- The source unrestricted sixteen-charge core-graph CLOSURE is exactly
the image of the genuine independent core-graph closure under the
same separately verified 17-slot fiber homeomorphism. -/
theorem sourceFullCoreGraph_closure_eq_independent_image_closure
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hColor : color = pairedAlgebraData.color)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w)) :
    closure (pairedAlgebraData.fullCoreGraph : Set
      (FullL2 2 × (SpinIndex → FullL2 2))) =
    (independentGraphTransportHomeomorph J) ''
      closure (independentFullCoreGraph color gamma theta : Set
        (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) := by
  calc
    closure (pairedAlgebraData.fullCoreGraph : Set
        (FullL2 2 × (SpinIndex → FullL2 2))) =
      closure ((independentGraphTransportHomeomorph J) ''
        (independentFullCoreGraph color gamma theta : Set
          (Lp E 2 μ × (SpinIndex → Lp E 2 μ)))) := by
        exact congrArg closure
          (sourceFullCoreGraph_eq_independent_image
            color gamma theta J hColor hGamma hJ)
    _ = (independentGraphTransportHomeomorph J) ''
        closure (independentFullCoreGraph color gamma theta : Set
          (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) :=
      ((independentGraphTransportHomeomorph J).image_closure
        (independentFullCoreGraph color gamma theta : Set
          (Lp E 2 μ × (SpinIndex → Lp E 2 μ)))).symm

#print axioms sourceFullCoreGraph_closure_eq_independent_image_closure

end
end FCP.IndependentSmoothSupercharge
