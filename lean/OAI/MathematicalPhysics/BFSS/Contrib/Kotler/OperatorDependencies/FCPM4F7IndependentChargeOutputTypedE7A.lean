import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F1TypedIndependentInvariantCharge
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentChargeVectorL2

/-!
M4F7 E7A — small *concrete* typed interface for independent SU(2)
invariant-core sixteen-charge outputs.

Three E7 gates showed the smooth core charge preservation statement
typechecks under the qualified M4F1 S2 source and representation witness,
while specialization to a concrete product-map range / E2 closed
operator can exhaust Lean's whnf budget.

This leaf isolates precisely the LinearMap.comp/subtype expression
appearing as the second component in E3's literal restricted-range
graph, without mentioning any closed graph, range witness, closure,
D1/G4K9D, source-transported operator, Hamiltonian or spectrum.

Neither CAR nor physical predicates, charge maps nor independent
definitions are changed. A green E7A is only a typed interface
certificate; **not** the E7 output-closedness theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F7IndependentChargeOutputTypedE7A
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentSmoothCore
open FCP.IndependentSmoothSupercharge
open FCP.IndependentPhysicalSpace
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

/-- The actual J-free independently defined BFSS charge-vector map
after composition with the genuine independent gauge-invariant core
subtype has every selected output in the genuine independent SU(2)
physical L² submodule. J remains solely a proof witness.

This precisely types the second component of E3's literal product map
but does not mention the closed operator or infer domain density. -/
theorem independentChargeVector_comp_invariantCore_output_physical
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
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (f : independentInvariantCore theta hCAR hHermitian)
    (α : SpinIndex) :
    (((independentChargeVector color gamma theta).comp
      (independentInvariantCore theta hCAR hHermitian).subtype) f) α ∈
        independentPhysicalSpace theta hCAR hHermitian := by
  have hSmooth :
      independentChargeVector color gamma theta f.val α ∈
        independentPhysicalSpace theta hCAR hHermitian := by
    have hq :=
      FCP.IndependentSmoothSupercharge.independentCharge_mem_invariantCore
        color gamma theta hCAR hHermitian J hColor hGamma hJ α f
    change independentCoreToL2
      (independentCharge color gamma theta α f.val) ∈
        independentPhysicalSpace theta hCAR hHermitian at hq
    change independentCoreToL2
      (independentCharge color gamma theta α f.val) ∈
        independentPhysicalSpace theta hCAR hHermitian
    exact hq
  have hsubtype :
      (independentInvariantCore theta hCAR hHermitian).subtype f = f.val := rfl
  simpa only [LinearMap.comp_apply, hsubtype] using hSmooth

#print axioms independentChargeVector_comp_invariantCore_output_physical
#check independentChargeVector_comp_invariantCore_output_physical

end
end FCP.M4F7IndependentChargeOutputTypedE7A
