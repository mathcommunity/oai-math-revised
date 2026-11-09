import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10AQOriginalGammaAnyOrientationForkRightLieBrackets

/-!
K1D18V10H-F10AR — arbitrary-orientation source gamma
bracket covariance and zero cases inside native so(16,R).

F10AP and F10AQ QUALIFIED all three nonzero bracket
overlap families on the ORIGINAL gamma matrices with
ANY three pairwise distinct source labels. F10AN
QUALIFIED disjoint pair brackets, originally on the
36 canonically ordered source gamma pairs. F10AO
QUALIFIED native self brackets on canonical pairs.

This small bridge closes orientation/zero bookkeeping
without claiming a full 36×36 bracket table: any
original gamma pair (a,b), a≠b, lives in the
accepted source-exact native so(16,R) carrier.
Reversing either input pair flips the native
Lie bracket sign; disjoint pairs have zero native
bracket regardless of orientation; and an arbitrary
source pair has zero self bracket.

Use only F10AP qualified sign reversal, F10AN
source matrix disjoint-commutator theorem,
and the Mathlib native Lie bracket laws
neg_lie, lie_neg, lie_self. No replacement source
gamma matrices, private tables or guessed signs.

A COMPLETE native so(9)->so(16) LieHom and the
exhaustive 36x36 canonical bracket formula are
NOT proved by this gate. Nor are 256 even
Clifford image independence/injection, Spin9 or
Spin48 global lifts, Fock action or BFSS physics.

FOUR exact declarations remain CANDIDATE until
frozen Lean warnings-as-errors compilation and
four independent type/root-axiom audits pass.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open OAI.BFSSQuantum
open Matrix

/-- Reversing the FIRST original gamma pair changes
the bracket sign inside the true native so(16,R). -/
theorem source9OriginalGamma_distinct_pair_first_reverse_bracket
    (a b c d : SpaceIndex)
    (hab : a ≠ b) (hcd : c ≠ d) :
    ⁅source9OriginalGammaDistinctPairInSo b a hab.symm,
      source9OriginalGammaDistinctPairInSo c d hcd⁆ =
      -⁅source9OriginalGammaDistinctPairInSo a b hab,
        source9OriginalGammaDistinctPairInSo c d hcd⁆ := by
  rw [source9OriginalGamma_distinct_pair_reverse_sign a b hab]
  simp only [neg_lie]

/-- Reversing the SECOND original gamma pair changes
the bracket sign inside the true native so(16,R). -/
theorem source9OriginalGamma_distinct_pair_second_reverse_bracket
    (a b c d : SpaceIndex)
    (hab : a ≠ b) (hcd : c ≠ d) :
    ⁅source9OriginalGammaDistinctPairInSo a b hab,
      source9OriginalGammaDistinctPairInSo d c hcd.symm⁆ =
      -⁅source9OriginalGammaDistinctPairInSo a b hab,
        source9OriginalGammaDistinctPairInSo c d hcd⁆ := by
  rw [source9OriginalGamma_distinct_pair_reverse_sign c d hcd]
  simp only [lie_neg]

/-- For ANY two original gamma pairs with four
distinct source labels (all cross inequalities),
their native Lie bracket is zero regardless of
whether a<b or b<a and c<d or d<c. -/
theorem source9OriginalGamma_distinct_disjoint_native_so_bracket_zero
    (a b c d : SpaceIndex)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    ⁅source9OriginalGammaDistinctPairInSo a b hab,
      source9OriginalGammaDistinctPairInSo c d hcd⁆ =
      (0 : LieAlgebra.Orthogonal.so SpinIndex ℝ) := by
  apply Subtype.ext
  change (gamma a * gamma b) * (gamma c * gamma d) -
    (gamma c * gamma d) * (gamma a * gamma b) =
      (0 : GammaMatrix)
  exact source9OriginalGamma_disjoint_pair_matrix_commutator_zero
    a b c d hac had hbc hbd

/-- Every original gamma pair with distinct labels
has zero self bracket, regardless of orientation,
inside the native Mathlib so(16,R). -/
theorem source9OriginalGamma_distinct_pair_native_so_self_bracket_zero
    (a b : SpaceIndex) (hab : a ≠ b) :
    ⁅source9OriginalGammaDistinctPairInSo a b hab,
      source9OriginalGammaDistinctPairInSo a b hab⁆ =
      (0 : LieAlgebra.Orthogonal.so SpinIndex ℝ) := by
  exact lie_self _

#print axioms source9OriginalGamma_distinct_pair_first_reverse_bracket
#print axioms source9OriginalGamma_distinct_pair_second_reverse_bracket
#print axioms source9OriginalGamma_distinct_disjoint_native_so_bracket_zero
#print axioms source9OriginalGamma_distinct_pair_native_so_self_bracket_zero

end
end FCP.BFSSPairedSpin9Clifford
