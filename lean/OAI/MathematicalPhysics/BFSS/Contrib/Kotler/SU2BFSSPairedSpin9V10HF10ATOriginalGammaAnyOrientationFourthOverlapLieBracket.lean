import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10ASOriginalGammaTotalTripleNativeLieBrackets

/-!
K1D18V10H-F10AT — original gamma pair FOURTH
cross-endpoint overlap a=d, including collision b=c.

Qualified F10AP, F10AQ and F10AS establish exact
original gamma native Lie chain, fork, shared-right,
reverse and collision identities. F10AT explicitly
supplies the remaining cross-endpoint orientation:
  [gamma_a gamma_b, gamma_c gamma_a] = +2 gamma_b gamma_c
for a,b,c pairwise distinct.

Proof: reverse the SECOND original gamma pair
using the pinned source anticommutation and the
F10AQ qualified shared-left fork identity. The
native so(16,R) theorem is the exact same original
matrix identity transported through Subtype.ext.

If b=c, the two original pair words are mutual
reversals and their bracket is zero, as qualified
in F10AS. Use a dependent-if total statement
for every input a!=b and c!=a.

This is a bounded interface required before a
single exhaustive canonical 36-by-36 bracket
classification. Neither a completed classifier
nor a native so(9)->so(16) LieHom is claimed.
No even-Clifford 256 independence/injection,
Spin9/Spin48 global lift, Fock representation
or BFSS physical/spectral result is claimed.
Three declarations are CANDIDATE pending strict
frozen Lean type and root axiom verification.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9DetFixture
open OAI.BFSSQuantum
open Matrix

/-- The fourth distinct three-source-index overlap:
in ORIGINAL real 16x16 gamma matrices, matching the
left endpoint of the first pair to the right endpoint
of the second gives positive twice gamma_b gamma_c. -/
theorem source9OriginalGamma_distinct_fourth_overlap_matrix_commutator
    (a b c : SpaceIndex)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (gamma a * gamma b) * (gamma c * gamma a) -
      (gamma c * gamma a) * (gamma a * gamma b) =
        (2 : ℝ) • (gamma b * gamma c) := by
  have hfork :=
    source9OriginalGamma_distinct_fork_matrix_commutator
      a b c hab hac hbc
  calc
    (gamma a * gamma b) * (gamma c * gamma a) -
        (gamma c * gamma a) * (gamma a * gamma b) =
        -((gamma a * gamma b) * (gamma a * gamma c) -
          (gamma a * gamma c) * (gamma a * gamma b)) := by
            rw [source9OriginalGamma_anticommute c a hac.symm]
            simp only [mul_neg, neg_mul]
            abel
    _ = -(-((2 : ℝ) • (gamma b * gamma c))) := by
          rw [hfork]
    _ = (2 : ℝ) • (gamma b * gamma c) := by
          simp only [neg_neg]

/-- Exact original gamma FOURTH cross-endpoint overlap
inside the true Mathlib native real so(16) carrier,
without any index ordering assumption. -/
theorem source9OriginalGamma_distinct_fourth_overlap_native_so_bracket
    (a b c : SpaceIndex)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ⁅source9OriginalGammaDistinctPairInSo a b hab,
      source9OriginalGammaDistinctPairInSo c a hac.symm⁆ =
      (2 : ℝ) • source9OriginalGammaDistinctPairInSo b c hbc := by
  apply Subtype.ext
  change (gamma a * gamma b) * (gamma c * gamma a) -
    (gamma c * gamma a) * (gamma a * gamma b) =
      (2 : ℝ) • (gamma b * gamma c)
  exact source9OriginalGamma_distinct_fourth_overlap_matrix_commutator
    a b c hab hac hbc

/-- The fourth cross-endpoint overlap is TOTAL under
the exact two inequalities defining its input pair
matrices. If b=c the native bracket is zero; otherwise
it is the accepted source-derived positive double. -/
theorem source9OriginalGamma_total_fourth_overlap_native_so_bracket
    (a b c : SpaceIndex) (hab : a ≠ b) (hca : c ≠ a) :
    ⁅source9OriginalGammaDistinctPairInSo a b hab,
      source9OriginalGammaDistinctPairInSo c a hca⁆ =
      if hbc : b = c then
        (0 : LieAlgebra.Orthogonal.so SpinIndex ℝ)
      else
        (2 : ℝ) • source9OriginalGammaDistinctPairInSo b c hbc := by
  by_cases hbc : b = c
  · subst c
    rw [dite_eq_left (show b = b from rfl)]
    exact source9OriginalGamma_distinct_pair_reverse_native_so_bracket_zero
      a b hab
  · simp only [dite_eq_right hbc]
    exact source9OriginalGamma_distinct_fourth_overlap_native_so_bracket
      a b c hab hca.symm hbc

#print axioms source9OriginalGamma_distinct_fourth_overlap_matrix_commutator
#print axioms source9OriginalGamma_distinct_fourth_overlap_native_so_bracket
#print axioms source9OriginalGamma_total_fourth_overlap_native_so_bracket

end
end FCP.BFSSPairedSpin9Clifford
