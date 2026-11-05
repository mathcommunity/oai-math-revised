import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10APOriginalGammaArbitraryOrientationNativeLieBridge

/-!
K1D18V10H-F10AQ — arbitrary-orientation shared-left
and shared-right original gamma-pair Lie brackets.

F10AP QUALIFIED the exact native original-source
gamma-pair carrier for arbitrary distinct orientations
and the universal three-distinct-index chain bracket:
  [gamma_a gamma_b, gamma_b gamma_c] = 2 gamma_a gamma_c.

Before tackling a 36×36 bracket assembly, use THAT
qualified theorem and a SINGLE source Clifford sign
reversal in each orientation to prove the two complementary
overlap identities for ANY pairwise distinct a,b,c:
  [gamma_a gamma_b, gamma_a gamma_c] = -2 gamma_b gamma_c
  [gamma_a gamma_c, gamma_b gamma_c] = -2 gamma_a gamma_b.

The proofs do not rederive gamma products through
private tables. Their matrix-level step rewrites
gamma_b gamma_a = -gamma_a gamma_b (respectively
gamma_c gamma_b = -gamma_b gamma_c), then transports
the already qualified F10AP arbitrary chain result.
Both identities are additionally stated on Mathlib's
actual so(16,R) subtype from F10AP, not a surrogate.

This is NOT a formal 36×36 bracket table, native so(9)
LieHom, even Clifford 256 gamma word linear independence
or injection, global Spin9/Spin48 lift, Fock module
or BFSS physics/spectral result. Those remain OPEN.

Four declarations are CANDIDATE pending strict frozen
Lean warnings-as-errors and independent exact type
and root axiom audits; no sorry/axioms/resource increases.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9DetFixture
open OAI.BFSSQuantum
open Matrix

/-- For ANY three pairwise distinct original source
labels, the shared-LEFT-index matrix commutator
is exactly minus two times the ORIGINAL gamma_b gamma_c.
This is F10AP chain with the first word reversed. -/
theorem source9OriginalGamma_distinct_fork_matrix_commutator
    (a b c : SpaceIndex)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (gamma a * gamma b) * (gamma a * gamma c) -
      (gamma a * gamma c) * (gamma a * gamma b) =
        -((2 : ℝ) • (gamma b * gamma c)) := by
  have hchain :=
    source9OriginalGamma_distinct_chain_matrix_commutator
      b a c hab.symm hbc hac
  calc
    (gamma a * gamma b) * (gamma a * gamma c) -
        (gamma a * gamma c) * (gamma a * gamma b) =
        -((gamma b * gamma a) * (gamma a * gamma c) -
          (gamma a * gamma c) * (gamma b * gamma a)) := by
            rw [source9OriginalGamma_anticommute b a hab.symm]
            simp only [neg_mul, mul_neg]
            abel
    _ = -((2 : ℝ) • (gamma b * gamma c)) := by
          rw [hchain]

/-- The same arbitrary-orientation shared-LEFT source
bracket INSIDE Mathlib's native real so(16) carrier. -/
theorem source9OriginalGamma_distinct_fork_native_so_bracket
    (a b c : SpaceIndex)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ⁅source9OriginalGammaDistinctPairInSo a b hab,
      source9OriginalGammaDistinctPairInSo a c hac⁆ =
      -((2 : ℝ) • source9OriginalGammaDistinctPairInSo b c hbc) := by
  apply Subtype.ext
  change (gamma a * gamma b) * (gamma a * gamma c) -
    (gamma a * gamma c) * (gamma a * gamma b) =
      -((2 : ℝ) • (gamma b * gamma c))
  exact source9OriginalGamma_distinct_fork_matrix_commutator
    a b c hab hac hbc

/-- For ANY three pairwise distinct original labels,
the shared-RIGHT-index matrix commutator is minus
two gamma_a gamma_b, using F10AP chain with the
second pair's orientation reversed. -/
theorem source9OriginalGamma_distinct_shared_right_matrix_commutator
    (a b c : SpaceIndex)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (gamma a * gamma c) * (gamma b * gamma c) -
      (gamma b * gamma c) * (gamma a * gamma c) =
        -((2 : ℝ) • (gamma a * gamma b)) := by
  have hchain :=
    source9OriginalGamma_distinct_chain_matrix_commutator
      a c b hac hab hbc.symm
  calc
    (gamma a * gamma c) * (gamma b * gamma c) -
        (gamma b * gamma c) * (gamma a * gamma c) =
        -((gamma a * gamma c) * (gamma c * gamma b) -
          (gamma c * gamma b) * (gamma a * gamma c)) := by
            rw [source9OriginalGamma_anticommute c b hbc.symm]
            simp only [mul_neg, neg_mul]
            abel
    _ = -((2 : ℝ) • (gamma a * gamma b)) := by
          rw [hchain]

/-- The same arbitrary-orientation shared-RIGHT
original gamma pair identity in native so(16,R). -/
theorem source9OriginalGamma_distinct_shared_right_native_so_bracket
    (a b c : SpaceIndex)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ⁅source9OriginalGammaDistinctPairInSo a c hac,
      source9OriginalGammaDistinctPairInSo b c hbc⁆ =
      -((2 : ℝ) • source9OriginalGammaDistinctPairInSo a b hab) := by
  apply Subtype.ext
  change (gamma a * gamma c) * (gamma b * gamma c) -
    (gamma b * gamma c) * (gamma a * gamma c) =
      -((2 : ℝ) • (gamma a * gamma b))
  exact source9OriginalGamma_distinct_shared_right_matrix_commutator
    a b c hab hac hbc

#print axioms source9OriginalGamma_distinct_fork_matrix_commutator
#print axioms source9OriginalGamma_distinct_fork_native_so_bracket
#print axioms source9OriginalGamma_distinct_shared_right_matrix_commutator
#print axioms source9OriginalGamma_distinct_shared_right_native_so_bracket

end
end FCP.BFSSPairedSpin9Clifford
