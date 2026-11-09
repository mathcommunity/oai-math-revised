import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10AROriginalGammaNativeBracketOrientationAndZeroBridge

/-!
F10AS — source-exact native original gamma pair brackets
for ALL triple-index overlaps, including repeated endpoints.

Accepted F10AP/F10AQ prove three native so(16,R) nonzero
bracket types for ANY pairwise distinct indices. F10AR
proves all source-pair reversal and self-bracket zero cases.
The formal 36x36 bracket classification still requires
integration of index collisions, not just separately
stated pairwise-distinct formulas.

This gate gives three dependent-if identities for
source-index triples under only the TWO inequalities
required to define the given input gamma pair words.
When the third inequality fails, the bracket MUST be
zero because the inputs coincide (fork/right) or are
reversed (chain). When it holds, reuse the EXACT
accepted arbitrary-orientation Lie theorem.

No global LieHom, all-pairs case assembly, even Clifford
256-image independence, Spin(9)/Spin(48) group lifts,
source Fock or BFSS physical results are claimed.
Four narrow candidate types, no sorry or added axioms.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open OAI.BFSSQuantum
open Matrix

/-- An original gamma pair and its reversed orientation
commute inside the ACTUAL native Mathlib so(16,R).
The reversed pair is the negative original by F10AP. -/
theorem source9OriginalGamma_distinct_pair_reverse_native_so_bracket_zero
    (a b : SpaceIndex) (hab : a ≠ b) :
    ⁅source9OriginalGammaDistinctPairInSo a b hab,
      source9OriginalGammaDistinctPairInSo b a hab.symm⁆ =
      (0 : LieAlgebra.Orthogonal.so SpinIndex ℝ) := by
  rw [source9OriginalGamma_distinct_pair_reverse_sign a b hab]
  simp only [lie_neg, lie_self, neg_zero]

/-- The native chain formula for EVERY a≠b and b≠c,
including the collision a=c that makes the two
original gamma pair words mutual negatives. -/
theorem source9OriginalGamma_total_chain_native_so_bracket
    (a b c : SpaceIndex) (hab : a ≠ b) (hbc : b ≠ c) :
    ⁅source9OriginalGammaDistinctPairInSo a b hab,
      source9OriginalGammaDistinctPairInSo b c hbc⁆ =
      if hac : a = c then
        (0 : LieAlgebra.Orthogonal.so SpinIndex ℝ)
      else
        (2 : ℝ) • source9OriginalGammaDistinctPairInSo a c hac := by
  by_cases hac : a = c
  · subst c
    rw [dite_eq_left (show a = a from rfl)]
    exact source9OriginalGamma_distinct_pair_reverse_native_so_bracket_zero
      a b hab
  · simp only [dite_eq_right hac]
    exact source9OriginalGamma_distinct_chain_native_so_bracket
      a b c hab hac hbc

/-- The native shared-left fork formula for every
a≠b, a≠c, including b=c: the same original
pair bracket is ZERO when the other endpoints agree. -/
theorem source9OriginalGamma_total_fork_native_so_bracket
    (a b c : SpaceIndex) (hab : a ≠ b) (hac : a ≠ c) :
    ⁅source9OriginalGammaDistinctPairInSo a b hab,
      source9OriginalGammaDistinctPairInSo a c hac⁆ =
      if hbc : b = c then
        (0 : LieAlgebra.Orthogonal.so SpinIndex ℝ)
      else
        -((2 : ℝ) • source9OriginalGammaDistinctPairInSo b c hbc) := by
  by_cases hbc : b = c
  · subst c
    rw [dite_eq_left (show b = b from rfl)]
    exact source9OriginalGamma_distinct_pair_native_so_self_bracket_zero
      a b hab
  · simp only [dite_eq_right hbc]
    exact source9OriginalGamma_distinct_fork_native_so_bracket
      a b c hab hac hbc

/-- The native shared-right formula for every
a≠c, b≠c, including a=b: when the first endpoints
agree the two input original gamma pairs coincide. -/
theorem source9OriginalGamma_total_shared_right_native_so_bracket
    (a b c : SpaceIndex) (hac : a ≠ c) (hbc : b ≠ c) :
    ⁅source9OriginalGammaDistinctPairInSo a c hac,
      source9OriginalGammaDistinctPairInSo b c hbc⁆ =
      if hab : a = b then
        (0 : LieAlgebra.Orthogonal.so SpinIndex ℝ)
      else
        -((2 : ℝ) • source9OriginalGammaDistinctPairInSo a b hab) := by
  by_cases hab : a = b
  · subst b
    rw [dite_eq_left (show a = a from rfl)]
    exact source9OriginalGamma_distinct_pair_native_so_self_bracket_zero
      a c hac
  · simp only [dite_eq_right hab]
    exact source9OriginalGamma_distinct_shared_right_native_so_bracket
      a b c hab hac hbc

#print axioms source9OriginalGamma_distinct_pair_reverse_native_so_bracket_zero
#print axioms source9OriginalGamma_total_chain_native_so_bracket
#print axioms source9OriginalGamma_total_fork_native_so_bracket
#print axioms source9OriginalGamma_total_shared_right_native_so_bracket

end
end FCP.BFSSPairedSpin9Clifford
