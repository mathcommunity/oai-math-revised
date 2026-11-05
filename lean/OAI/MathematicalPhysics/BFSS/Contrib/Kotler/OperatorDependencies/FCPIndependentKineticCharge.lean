import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentCoordinateDerivative

/-!
M4E3 — independently specified BFSS kinetic supercharge component.

For arbitrary real nine gamma matrices supplied as input and the genuine
independent 48-Majorana family, define the exact finite sum of
(-i gamma) times independent fermion multiplication AFTER the
independent smooth coordinate derivative.

No J or original source charge appears in that definition. The
source gamma matching condition and M3J generator intertwiner occur
only in the proof of identification with the first (kinetic) summand
of the literal pinned AlgebraData.charge.

The cubic potential, full sixteen charges, closure, Hamiltonian and
spectrum remain distinct unproved boundaries.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.IndependentSmoothSupercharge
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.IndependentSmoothCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

/-- Direct independent kinetic differential expression:
the order is fermion multiplication AFTER the spatial derivative,
with the manuscript's exact -i gamma coefficient. -/
def independentKineticCharge
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (α : SpinIndex) :
    IndependentTestCore E →ₗ[ℂ] IndependentTestCore E :=
  ∑ i : SpaceIndex, ∑ A : ColorIndex 2, ∑ β : SpinIndex,
    (-Complex.I * (gamma i α β : ℂ)) •
      ((independentFermionCoreAction theta β A).comp
        (independentCoordinateDerivative i A))

/-- Exact intertwining with the genuine FIRST (kinetic) summand of the
original `AlgebraData.charge` definition, with independently defined
gamma and theta factors; no charge is constructed by conjugation. -/
theorem independentKineticCharge_intertwining
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (α : SpinIndex) (f : IndependentTestCore E) :
    independentSmoothTransport J (independentKineticCharge gamma theta α f) =
      (∑ i : SpaceIndex, ∑ A : ColorIndex 2, ∑ β : SpinIndex,
        (-Complex.I * (pairedAlgebraData.gamma i α β : ℂ)) •
          ((pairedAlgebraData.fermionAction β A).comp
            (coordinateDerivative i A)))
        (independentSmoothTransport J f) := by
  subst gamma
  have hterm (i : SpaceIndex) (A : ColorIndex 2) (β : SpinIndex) :
      independentSmoothTransport J
        (independentFermionCoreAction theta β A
          (independentCoordinateDerivative i A f)) =
      pairedAlgebraData.fermionAction β A
        (coordinateDerivative i A (independentSmoothTransport J f)) := by
    rw [independentFermionCoreAction_intertwining theta J hJ β A
      (independentCoordinateDerivative i A f)]
    rw [independentCoordinateDerivative_intertwining J i A f]
  simp only [independentKineticCharge,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    map_sum, map_smul]
  simp_rw [hterm]

#print axioms independentKineticCharge
#print axioms independentKineticCharge_intertwining

end
end FCP.IndependentSmoothSupercharge
