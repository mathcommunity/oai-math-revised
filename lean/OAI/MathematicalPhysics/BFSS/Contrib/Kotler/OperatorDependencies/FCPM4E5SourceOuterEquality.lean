import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4E5SourceParts

/-!
M4E5 proof architecture diagnostic B: establish the exact OUTER
addition of the original AlgebraData.charge for completely abstract
M : AlgebraData N, avoiding specialized BFSS matrices and Majoranas.

This tests whether identifying the two named source components with
the literal pinned source charge can be kernel checked separately.
It does not prove the independent full sixteen-charge intertwiner.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.IndependentSmoothSupercharge
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData

/-- Exact frozen original BFSS source charge equals the outer addition
of its two named source-exact components, for arbitrary M and N. -/
theorem originalSource_charge_eq_parts {N : ℕ}
    (M : AlgebraData N) (α : SpinIndex) :
    M.charge α =
      originalSourceKineticPart M α + originalSourceCubicPart M α := by
  rfl

/-- Pointwise application: only the outer LinearMap addition. -/
theorem originalSource_charge_apply_parts {N : ℕ}
    (M : AlgebraData N) (α : SpinIndex) (f : SmoothCore N) :
    M.charge α f =
      originalSourceKineticPart M α f +
        originalSourceCubicPart M α f := by
  rw [originalSource_charge_eq_parts M α, LinearMap.add_apply]

#print axioms originalSource_charge_eq_parts
#print axioms originalSource_charge_apply_parts

end
end FCP.IndependentSmoothSupercharge
