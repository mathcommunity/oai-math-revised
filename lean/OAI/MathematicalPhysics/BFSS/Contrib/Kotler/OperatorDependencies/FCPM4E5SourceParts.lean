import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentCubicCharge

/-!
M4E5 proof architecture diagnostic A: two source-exact NAMED kinetic and
cubic linear maps for an ABSTRACT AlgebraData N, never the concrete
pairedAlgebraData at definition time. Exact same coefficients, index
order, casts and composition as the pinned original AlgebraData.charge.

This module does not attempt the independent full charge theorem or
modify the original etblink/math source. It intentionally keeps M abstract
so that no Clifford, color, Fock or Finset internals are reduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.IndependentSmoothSupercharge
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData

/-- Literal first summand of the frozen original charge for arbitrary
original AlgebraData; no separate normalization or convention. -/
def originalSourceKineticPart {N : ℕ} (M : AlgebraData N) (α : SpinIndex) :
    SmoothCore N →ₗ[ℂ] SmoothCore N :=
  ∑ i : SpaceIndex, ∑ A : ColorIndex N, ∑ β : SpinIndex,
    (-Complex.I * (M.gamma i α β : ℂ)) •
      ((M.fermionAction β A).comp (coordinateDerivative i A))

/-- Literal second (cubic) summand of the frozen original charge.
Preserves the original source 1/2, all six summation labels and
theta ∘ position i B ∘ position j C ordering. -/
def originalSourceCubicPart {N : ℕ} (M : AlgebraData N) (α : SpinIndex) :
    SmoothCore N →ₗ[ℂ] SmoothCore N :=
  ∑ i : SpaceIndex, ∑ j : SpaceIndex, ∑ A : ColorIndex N,
    ∑ B : ColorIndex N, ∑ C : ColorIndex N, ∑ β : SpinIndex,
    (((1 / 2 : ℝ) * M.structureConstant A B C * M.gammaTwo i j α β : ℝ) : ℂ) •
      ((M.fermionAction β A).comp ((position i B).comp (position j C)))

#print axioms originalSourceKineticPart
#print axioms originalSourceCubicPart

end
end FCP.IndependentSmoothSupercharge
