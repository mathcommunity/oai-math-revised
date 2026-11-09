import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10ATOriginalGammaAnyOrientationFourthOverlapLieBracket

/-!
K1D18V10H-F10AU — EXHAUSTIVE original gamma pair
bracket classification for all oriented distinct pairs
inside Mathlib's TRUE native so(16,R).

The accepted F10AS and F10AT dependent-if overlap
identities, F10AQ universal three-index formulas,
F10AR arbitrary disjoint-pair zero, and F10AP
source-exact oriented carrier jointly make possible
ONE theorem over every (a,b) and (c,d) with a≠b
and c≠d. No ordering of these four source labels
is required; this is stronger in domain than the
36x36 canonical-pair bracket table.

The complete case order is:
  1. a=c: shared-left fork, including b=d collision;
  2. b=c: chain, including a=d reversal collision;
  3. b=d: shared-right, with a≠c;
  4. a=d: fourth overlap, with b≠c;
  5. otherwise: all four cross labels distinct,
     the commutator vanishes.

Dependent-if RHS preserves exact output source pair
typing; DO NOT assume an output pair exists if its
two indices coincide. Use only source gamma matrices
and qualified native Lie algebra theorem declarations.

A formal source-exact native so(9)->so(16) LieHom
is NOT constructed here. Nor is even Clifford 256
PBW independence/injection, Spin group lift, BFSS
Fock operator or spectral/physical content claimed.

CANDIDATE until strict Lean 4.34.1/Mathlib source
pinning, warnings-as-errors compile and independent
complete statement type/root-axiom audits succeed.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open OAI.BFSSQuantum
open Matrix

/-- Exhaustive FIVE-WAY native source gamma-pair
Lie bracket formula for ANY two distinct ORIGINAL
gamma-pair labels, including ALL overlap, repeated-
pair, reversed-pair and four-distinct cases.

Priority is source-index equality a=c, then b=c,
then b=d, then a=d, else all cross pairs disjoint.
The first two branches include their precise
dependent-if zero-collision alternatives. -/
theorem source9OriginalGamma_exhaustive_oriented_pair_native_so_bracket
    (a b c d : SpaceIndex) (hab : a ≠ b) (hcd : c ≠ d) :
    ⁅source9OriginalGammaDistinctPairInSo a b hab,
      source9OriginalGammaDistinctPairInSo c d hcd⁆ =
      if hac : a = c then
        if hbd : b = d then
          (0 : LieAlgebra.Orthogonal.so SpinIndex ℝ)
        else
          -((2 : ℝ) • source9OriginalGammaDistinctPairInSo b d hbd)
      else if hbc : b = c then
        if had : a = d then
          (0 : LieAlgebra.Orthogonal.so SpinIndex ℝ)
        else
          (2 : ℝ) • source9OriginalGammaDistinctPairInSo a d had
      else if _hbd : b = d then
        -((2 : ℝ) • source9OriginalGammaDistinctPairInSo a c hac)
      else if _had : a = d then
        (2 : ℝ) • source9OriginalGammaDistinctPairInSo b c hbc
      else
        (0 : LieAlgebra.Orthogonal.so SpinIndex ℝ) := by
  by_cases hac : a = c
  · subst c
    rw [dite_eq_left (show a = a from rfl)]
    exact source9OriginalGamma_total_fork_native_so_bracket
      a b d hab hcd
  · rw [dite_eq_right hac]
    by_cases hbc : b = c
    · subst c
      rw [dite_eq_left (show b = b from rfl)]
      exact source9OriginalGamma_total_chain_native_so_bracket
        a b d hab hcd
    · rw [dite_eq_right hbc]
      by_cases hbd : b = d
      · subst d
        rw [dite_eq_left (show b = b from rfl)]
        exact source9OriginalGamma_distinct_shared_right_native_so_bracket
          a c b hac hab hcd
      · rw [dite_eq_right hbd]
        by_cases had : a = d
        · subst d
          rw [dite_eq_left (show a = a from rfl)]
          exact source9OriginalGamma_distinct_fourth_overlap_native_so_bracket
            a b c hab hac hbc
        · rw [dite_eq_right had]
          exact source9OriginalGamma_distinct_disjoint_native_so_bracket_zero
            a b c d hab hcd hac had hbc hbd

#print axioms source9OriginalGamma_exhaustive_oriented_pair_native_so_bracket

end
end FCP.BFSSPairedSpin9Clifford
