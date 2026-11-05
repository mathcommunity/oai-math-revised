import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9FourIndexDiagonalBoundaryProbe

/-!
K1D18V8K — source-original paired Spin(9) four-index repeated-pair cases.

V8J settles r=s and t=u diagonal planes. This next isolated boundary
settles (r,s)=(t,u) and (r,s)=(u,t), assuming r != s, with the EXACT
source-native zero-diagonal 48-real L matrices, RHS and V8H orientation.
The full four-index universal bracket remains a separate obligation.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum

/-- Exact source-native four-index RHS vanishes for identical oriented pairs. -/
theorem zeroDiagonalFourIndexRHS_same_pair
    (r s : SpaceIndex) (hrs : r ≠ s) :
    zeroDiagonalFourIndexRHS r s r s = 0 := by
  simp [zeroDiagonalFourIndexRHS, hrs, Ne.symm hrs,
    zeroDiagonalPairedPlane_self]

/-- Exact source-native four-index RHS vanishes for reversed oriented pairs. -/
theorem zeroDiagonalFourIndexRHS_reverse_pair
    (r s : SpaceIndex) (hrs : r ≠ s) :
    zeroDiagonalFourIndexRHS r s s r = 0 := by
  simp [zeroDiagonalFourIndexRHS, hrs, Ne.symm hrs,
    zeroDiagonalPairedPlane_self]

/-- The identical-pair commutator is the exact original-label RHS. -/
theorem zeroDiagonalFourIndex_same_pair_bracket
    (r s : SpaceIndex) (hrs : r ≠ s) :
    zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane r s -
        zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane r s =
      zeroDiagonalFourIndexRHS r s r s := by
  rw [zeroDiagonalFourIndexRHS_same_pair r s hrs]
  exact sub_self _

/-- The reversed-pair commutator is the exact original-label RHS. -/
theorem zeroDiagonalFourIndex_reverse_pair_bracket
    (r s : SpaceIndex) (hrs : r ≠ s) :
    zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane s r -
        zeroDiagonalPairedPlane s r * zeroDiagonalPairedPlane r s =
      zeroDiagonalFourIndexRHS r s s r := by
  rw [zeroDiagonalFourIndexRHS_reverse_pair r s hrs,
    zeroDiagonalPairedPlane_swap r s]
  simp only [mul_neg, neg_mul, sub_self]

#print axioms zeroDiagonalFourIndexRHS_same_pair
#print axioms zeroDiagonalFourIndexRHS_reverse_pair
#print axioms zeroDiagonalFourIndex_same_pair_bracket
#print axioms zeroDiagonalFourIndex_reverse_pair_bracket

end
end FCP.BFSSPairedSpin9Plane
