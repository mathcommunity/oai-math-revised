import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentFullSmoothCharge

/-!
M4F2 (candidate, NOT qualified) — the genuinely independent BFSS
sixteen-charge L² column on the E-valued smooth test core and its
exact source chargeVector transport.

This is an L² test-core vector identity; it does not establish
closed graphs or physical domains. The independent operator definition
is J-free, and proof reuses strictly accepted M4E5 source equality.
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

/-- Independently defined original sixteen-charge column, evaluated
on E-valued compactly supported smooth sections and embedded in L².
No J, reference Fock source operator, or assumed physical graph. -/
def independentChargeVector
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E) :
    IndependentTestCore E →ₗ[ℂ] (SpinIndex → Lp E 2 μ) :=
  LinearMap.pi (fun α =>
    independentCoreToL2.comp (independentCharge color gamma theta α))

/-- Exact source L² charge-column component transport for arbitrary
spin α under the accepted original Clifford/Majorana matching. -/
theorem independentChargeVector_component_intertwining
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hColor : color = pairedAlgebraData.color)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (α : SpinIndex) (f : IndependentTestCore E) :
    fiberTransport J (independentChargeVector color gamma theta f α) =
      pairedAlgebraData.chargeVector (independentSmoothTransport J f) α := by
  change fiberTransport J
      (independentCoreToL2 (independentCharge color gamma theta α f)) =
    pairedAlgebraData.chargeVector (independentSmoothTransport J f) α
  calc
    fiberTransport J (independentCoreToL2 (independentCharge color gamma theta α f)) =
      coreToL2 (independentSmoothTransport J
        (independentCharge color gamma theta α f)) :=
        independentSmoothTransport_coreToL2 J _
    _ = coreToL2 (pairedAlgebraData.charge α (independentSmoothTransport J f)) :=
      congrArg coreToL2
        (independentCharge_intertwining color gamma theta J hColor hGamma hJ α f)
    _ = pairedAlgebraData.chargeVector (independentSmoothTransport J f) α := by
      simp only [AlgebraData.chargeVector, LinearMap.pi_apply, LinearMap.comp_apply]

#print axioms independentChargeVector
#print axioms independentChargeVector_component_intertwining

end
end FCP.IndependentSmoothSupercharge
