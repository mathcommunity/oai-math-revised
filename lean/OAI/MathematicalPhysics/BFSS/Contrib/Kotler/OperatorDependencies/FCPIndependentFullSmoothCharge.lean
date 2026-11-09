import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4E5NamedKineticBridge
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4E5NamedCubicBridge

/-!
M4E5 — source-exact independent sixteen smooth BFSS supercharges.

Independent construction: genuine E-valued kinetic PLUS cubic charge,
using independently specified gamma matrices, color matrices, and
Majorana maps. The definition does not use the original Fock charge or
the fiber equivalence J.

Proof: combine strictly qualified named kinetic and cubic transports
with the independently accepted originalSource_charge_apply_parts
outer-add theorem. No raw source multivariate finite sums are unfolded.
This is a smooth-core identity only, not closed or gauge-restricted
supercharges, Hamiltonian equality or spectrum.
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

/-- All sixteen independent E-valued smooth BFSS supercharges.
The construction has NO dependence on a fiber equivalence J or
the original pinned Fock source charge. -/
def independentCharge
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (α : SpinIndex) :
    IndependentTestCore E →ₗ[ℂ] IndependentTestCore E :=
  independentKineticCharge gamma theta α +
    independentCubicCharge color gamma theta α

/-- Source-exact equality at every spin index, proved by composing
named, independently verified component intertwining theorems and
the original source's abstractly verified outer-addition identity. -/
theorem independentCharge_intertwining
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hColor : color = pairedAlgebraData.color)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (α : SpinIndex) (f : IndependentTestCore E) :
    independentSmoothTransport J (independentCharge color gamma theta α f) =
      pairedAlgebraData.charge α (independentSmoothTransport J f) := by
  calc
    independentSmoothTransport J (independentCharge color gamma theta α f)
        =
        independentSmoothTransport J (independentKineticCharge gamma theta α f) +
          independentSmoothTransport J
            (independentCubicCharge color gamma theta α f) := by
          simp only [independentCharge, LinearMap.add_apply, map_add]
    _ =
        originalSourceKineticPart pairedAlgebraData α
          (independentSmoothTransport J f) +
        originalSourceCubicPart pairedAlgebraData α
          (independentSmoothTransport J f) := by
          exact congrArg₂
            (fun (u v : SmoothCore 2) => u + v)
            (independentKinetic_named_source_intertwining
              gamma theta J hGamma hJ α f)
            (independentCubic_named_source_intertwining
              color gamma theta J hColor hGamma hJ α f)
    _ = pairedAlgebraData.charge α (independentSmoothTransport J f) :=
          (originalSource_charge_apply_parts
            pairedAlgebraData α (independentSmoothTransport J f)).symm

#print axioms independentCharge
#print axioms independentCharge_intertwining
#check independentCharge_intertwining

end
end FCP.IndependentSmoothSupercharge
