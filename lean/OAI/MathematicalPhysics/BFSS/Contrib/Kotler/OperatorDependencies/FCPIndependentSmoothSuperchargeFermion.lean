import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentGaugePointwise

/-!
M4E1 — independently specified fermionic multiplication on the actual
E-valued smooth compactly supported BFSS test functions.

The operator is defined directly from the 48 independent Hermitian
Majorana maps, without selecting J or transporting a source charge.
The accepted M3J generator-preserving unitary is used only in the
proof establishing source-exact fermionic test-function intertwining.
This is the first building block for the independent kinetic and cubic
BFSS supercharge expressions. No full supercharge/graph/domain
or spectral identity is asserted.
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

/-- Direct independent Majorana multiplication on genuinely E-valued
smooth test functions, using the finite-dimensional continuous-linear
form of the originally supplied independent Majorana operator. -/
def independentFermionCoreAction
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (β : SpinIndex) (A : ColorIndex 2) :
    IndependentTestCore E →ₗ[ℂ] IndependentTestCore E :=
  (TestFunction.postcompCLM
    ((Module.End.toContinuousLinearMap E) (theta β A))).toLinearMap

/-- Actual pointwise action of the independently defined operator. -/
theorem independentFermionCoreAction_apply
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (β : SpinIndex) (A : ColorIndex 2)
    (f : IndependentTestCore E) (x : Boson 2) :
    independentFermionCoreAction theta β A f x = theta β A (f x) := by
  rfl

/-- Source-exact intertwining at the literal smooth test-function
level, for the independently constructed Majorana multiplication and
the original AlgebraData.fermionAction. This uses the original
pairedAlgebraData theta and does not define independent operators
through J. -/
theorem independentFermionCoreAction_intertwining
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (β : SpinIndex) (A : ColorIndex 2) (f : IndependentTestCore E) :
    independentSmoothTransport J (independentFermionCoreAction theta β A f) =
      pairedAlgebraData.fermionAction β A (independentSmoothTransport J f) := by
  apply DFunLike.ext
  intro x
  change J (theta β A (f x)) =
    pairedAlgebraData.theta β A (J (f x))
  rw [pairedAlgebraData_theta]
  exact hJ β A (f x)

#print axioms independentFermionCoreAction
#print axioms independentFermionCoreAction_apply
#print axioms independentFermionCoreAction_intertwining

end
end FCP.IndependentSmoothSupercharge
