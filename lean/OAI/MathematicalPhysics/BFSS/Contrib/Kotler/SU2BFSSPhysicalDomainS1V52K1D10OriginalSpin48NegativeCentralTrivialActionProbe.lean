import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D9OriginalSpin48NegativeCentralMembershipProbe

/-!
K1D10 — genuine original Spin(48) negative-central real-vector action.

Accepted K1D9 establishes that -1 belongs to the exact source
spinGroup source48Quadratic. We use the original S1V31 vector action
defined from canonical Clifford conjugation, not a stand-in SO action.

The second root verifies that this actual negative-central Spin element
fixes all 48-real source vectors. No full kernel classification is
claimed until separately composed with the accepted K1D8 upper bound.
CANDIDATE ONLY until new strict owner CI passes.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace FCP.BFSSS1V52K1D10
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- The actual S1V31 source vector action is Clifford conjugation by
the genuine Spin group element, with inverse supplied by Clifford star
through the pinned Mathlib spinGroup.toUnits definition. -/
theorem originalSourceSpin48VectorAction_clifford_star
    (s : spinGroup Q) (v : Source48Vector) :
    CliffordAlgebra.ι Q (FCP.BFSSS1V31.sourceSpin48VectorAction s v) =
      (s : C) * CliffordAlgebra.ι Q v * star (s : C) := by
  rw [FCP.BFSSS1V31.sourceSpin48VectorAction_clifford_generator]
  change (s : C) * CliffordAlgebra.ι Q v * ((s⁻¹ : spinGroup Q) : C) =
    (s : C) * CliffordAlgebra.ι Q v * star (s : C)
  rfl

/-- The unconditionally admitted negative-central element from K1D9
acts trivially on every original 48-real source vector. -/
theorem originalSourceSpin48_negativeCentral_trivialAction
    (v : Source48Vector) :
    FCP.BFSSS1V31.sourceSpin48VectorAction
      (⟨-1, FCP.BFSSS1V52K1D9.originalSourceSpin48_neg_one_mem⟩ : spinGroup Q) v = v := by
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  rw [originalSourceSpin48VectorAction_clifford_star]
  simp

#print axioms originalSourceSpin48VectorAction_clifford_star
#print axioms originalSourceSpin48_negativeCentral_trivialAction

end
end FCP.BFSSS1V52K1D10
