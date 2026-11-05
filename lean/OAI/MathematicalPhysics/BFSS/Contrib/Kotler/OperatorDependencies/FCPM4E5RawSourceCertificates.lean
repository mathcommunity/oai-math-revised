import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4E5SourceOuterEquality

/-!
M4E5 bounded bridge architecture: abstract named-vs-raw source operator
equalities proved BEFORE specializing the source data to concrete SU(2).

No transport, original pairedAlgebraData or independent charge is used
in these definitions. This module adds ONLY an explicit rewriting
certificate for the two literal finite sums already present in the
pinned original charge definition.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.IndependentSmoothSupercharge
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData

/-- Equality between the accepted named original kinetic operator
and the literal kinetic source finite sum for ABSTRACT AlgebraData. -/
theorem originalSourceKineticPart_eq_sum {N : ℕ}
    (M : AlgebraData N) (α : SpinIndex) :
    originalSourceKineticPart M α =
      (∑ i : SpaceIndex, ∑ A : ColorIndex N, ∑ β : SpinIndex,
        (-Complex.I * (M.gamma i α β : ℂ)) •
          ((M.fermionAction β A).comp (coordinateDerivative i A))) := by
  rfl

/-- Equality between the accepted named original cubic operator
and the literal cubic finite sum, still for ABSTRACT AlgebraData. -/
theorem originalSourceCubicPart_eq_sum {N : ℕ}
    (M : AlgebraData N) (α : SpinIndex) :
    originalSourceCubicPart M α =
      (∑ i : SpaceIndex, ∑ j : SpaceIndex, ∑ A : ColorIndex N,
        ∑ B : ColorIndex N, ∑ C : ColorIndex N, ∑ β : SpinIndex,
        (((1 / 2 : ℝ) * M.structureConstant A B C *
          M.gammaTwo i j α β : ℝ) : ℂ) •
            ((M.fermionAction β A).comp
              ((position i B).comp (position j C)))) := by
  rfl

#print axioms originalSourceKineticPart_eq_sum
#print axioms originalSourceCubicPart_eq_sum

end
end FCP.IndependentSmoothSupercharge
