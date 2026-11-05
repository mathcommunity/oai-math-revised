import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9ZeroDiagonalInterfaceProbe

/-!
K1D18V8J — four-index Spin(9) RHS: original paired-label diagonal boundary.

The exact source-native generator is L(r,s) = if r=s then 0 else K(r,s).
This module defines the delta-weighted candidate all-indices RHS using
typed decidable-equality branches, NOT an unproved matrix / basis isomorphism.

It proves that either degenerate input plane has zero candidate RHS and
that the actual L-matrix commutator also agrees in these two cases.

These are preliminary boundary identities, NOT the universal four-index
bracket theorem or an integrated Spin(9) group action. No limits increased.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0

/-- The EXACT 2-delta four-index candidate RHS on the native Fock paired
48-real label matrix. (Matrix addition is written explicitly instead of
requiring any unproved type/field coercion.) -/
noncomputable def zeroDiagonalFourIndexRHS
    (r s t u : SpaceIndex) : Matrix Source48Label Source48Label ℝ :=
  (if s = u then zeroDiagonalPairedPlane r t + zeroDiagonalPairedPlane r t else 0) -
  (if s = t then zeroDiagonalPairedPlane r u + zeroDiagonalPairedPlane r u else 0) +
  (if r = t then zeroDiagonalPairedPlane s u + zeroDiagonalPairedPlane s u else 0) -
  (if r = u then zeroDiagonalPairedPlane s t + zeroDiagonalPairedPlane s t else 0)

/-- The proposed universal RHS correctly vanishes for a left diagonal plane. -/
theorem zeroDiagonalFourIndexRHS_left_self (r t u : SpaceIndex) :
    zeroDiagonalFourIndexRHS r r t u = 0 := by
  by_cases hrt : r = t <;> by_cases hru : r = u
  all_goals simp [zeroDiagonalFourIndexRHS, hrt, hru]

/-- The proposed universal RHS correctly vanishes for a right diagonal plane. -/
theorem zeroDiagonalFourIndexRHS_right_self (r s t : SpaceIndex) :
    zeroDiagonalFourIndexRHS r s t t = 0 := by
  by_cases hst : s = t <;> by_cases hrt : r = t
  all_goals simp [zeroDiagonalFourIndexRHS, hst, hrt]

/-- Exact source-native four-index bracket in the left diagonal case. -/
theorem zeroDiagonalFourIndex_left_self_bracket (r t u : SpaceIndex) :
    zeroDiagonalPairedPlane r r * zeroDiagonalPairedPlane t u -
      zeroDiagonalPairedPlane t u * zeroDiagonalPairedPlane r r =
        zeroDiagonalFourIndexRHS r r t u := by
  rw [zeroDiagonalPairedPlane_self, zeroDiagonalFourIndexRHS_left_self]
  simp

/-- Exact source-native four-index bracket in the right diagonal case. -/
theorem zeroDiagonalFourIndex_right_self_bracket (r s t : SpaceIndex) :
    zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane t t -
      zeroDiagonalPairedPlane t t * zeroDiagonalPairedPlane r s =
        zeroDiagonalFourIndexRHS r s t t := by
  rw [zeroDiagonalPairedPlane_self, zeroDiagonalFourIndexRHS_right_self]
  simp

#print axioms zeroDiagonalFourIndexRHS_left_self
#print axioms zeroDiagonalFourIndexRHS_right_self
#print axioms zeroDiagonalFourIndex_left_self_bracket
#print axioms zeroDiagonalFourIndex_right_self_bracket

end
end FCP.BFSSPairedSpin9Plane
