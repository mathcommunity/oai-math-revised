import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10AOOriginalGammaPairReverseAndSelfLieBrackets

/-!
K1D18V10H-F10AP — source-exact arbitrary orientation
bridge from the ORIGINAL gamma pair words into native
Mathlib so(16,R) and first arbitrary-label chain bracket.

F10AJ qualifies all 36 canonically indexed (a<b)
original gamma pairs as linearly independent elements of
the native so(16,R). F10AK–F10AO qualify the ordered,
reversed, same-pair and disjoint bracket families.

The next obstacle to a FULL native 36x36 bracket formula is
reconciling arbitrary label orientations and hypotheses
without silently guessing signs. Establish an ACTUAL
native so(16,R) carrier for gamma_a gamma_b whenever a!=b,
prove reversal changes the sign, and prove equality with
F10AJ's canonical carrier when a<b.

Then verify the nontrivial chain bracket for ANY three
pairwise distinct ORIGINAL source indices in arbitrary
order (not only a<b<c):
  [gamma_a gamma_b, gamma_b gamma_c] = 2 gamma_a gamma_c.

No full pair-bracket case assembly, source so(9) LieHom,
global Spin9 or Spin48 lift, full even Clifford 256 image
independence/injectivity, source Fock operator or BFSS
physical/spectral result is claimed. All are still OPEN.

Only accepted PUBLIC original gamma symmetry,
anticommutation, gamma square and Mathlib native
LieSubalgebra are used; no replacement gamma tables,
new axioms, sorry or higher resource limits.
CANDIDATE until strict frozen compiler and SIX exact
declaration-type/root-axiom audits pass.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9DetFixture
open OAI.BFSSQuantum
open Matrix

/-- An original gamma_a gamma_b word is skew-symmetric
for ANY two distinct source labels, regardless of order. -/
theorem source9OriginalGamma_distinct_pair_transpose_neg
    (a b : SpaceIndex) (hab : a ≠ b) :
    (gamma a * gamma b).transpose = -(gamma a * gamma b) := by
  rw [Matrix.transpose_mul]
  rw [gamma_symmetric b, gamma_symmetric a]
  exact source9OriginalGamma_anticommute b a hab.symm

/-- The original pair product lies in the pinned Mathlib
orthogonal LieSubalgebra for ANY distinct a,b. -/
theorem source9OriginalGamma_distinct_pair_mem_so
    (a b : SpaceIndex) (hab : a ≠ b) :
    gamma a * gamma b ∈ LieAlgebra.Orthogonal.so SpinIndex ℝ := by
  rw [LieAlgebra.Orthogonal.mem_so]
  exact source9OriginalGamma_distinct_pair_transpose_neg a b hab

/-- The actual original gamma word as a member of
native Mathlib so(16,R), with arbitrary orientation. -/
def source9OriginalGammaDistinctPairInSo
    (a b : SpaceIndex) (hab : a ≠ b) :
    LieAlgebra.Orthogonal.so SpinIndex ℝ :=
  ⟨gamma a * gamma b,
   source9OriginalGamma_distinct_pair_mem_so a b hab⟩

/-- Exchanging two distinct original gamma labels
negates the actual element in native so(16,R). -/
theorem source9OriginalGamma_distinct_pair_reverse_sign
    (a b : SpaceIndex) (hab : a ≠ b) :
    source9OriginalGammaDistinctPairInSo b a hab.symm =
      -(source9OriginalGammaDistinctPairInSo a b hab) := by
  apply Subtype.ext
  change gamma b * gamma a = -(gamma a * gamma b)
  exact source9OriginalGamma_anticommute b a hab.symm

/-- The arbitrary-orientation carrier AGREES EXACTLY
with the previously qualified 36 canonical-source-pair
native so(16,R) representative whenever a<b. -/
theorem source9OriginalGamma_distinct_pair_agrees_ordered
    (a b : SpaceIndex) (hab : a < b) :
    source9OriginalGammaDistinctPairInSo a b (ne_of_lt hab) =
      source9OrderedGammaPairInSo ⟨(a,b),hab⟩ := by
  apply Subtype.ext
  rfl

/-- Exact original-source matrix chain commutator for
ANY three pairwise distinct labels in arbitrary order.
The coefficient two is source-derived, not guessed. -/
theorem source9OriginalGamma_distinct_chain_matrix_commutator
    (a b c : SpaceIndex)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (gamma a * gamma b) * (gamma b * gamma c) -
      (gamma b * gamma c) * (gamma a * gamma b) =
        (2 : ℝ) • (gamma a * gamma c) := by
  have hba : b ≠ a := hab.symm
  have hca : c ≠ a := hac.symm
  have hforward :
      (gamma a * gamma b) * (gamma b * gamma c) =
        gamma a * gamma c := by
    calc
      (gamma a * gamma b) * (gamma b * gamma c) =
          gamma a * ((gamma b * gamma b) * gamma c) := by
            simp only [mul_assoc]
      _ = gamma a * gamma c := by
            rw [source9OriginalGamma_basis_mul_self b, one_mul]
  have hreverse :
      (gamma b * gamma c) * (gamma a * gamma b) =
        -(gamma a * gamma c) := by
    calc
      (gamma b * gamma c) * (gamma a * gamma b) =
          (gamma b * (gamma c * gamma a)) * gamma b := by
            simp only [mul_assoc]
      _ = (gamma b * (-(gamma a * gamma c))) * gamma b := by
            rw [source9OriginalGamma_anticommute c a hca]
      _ = -((gamma b * (gamma a * gamma c)) * gamma b) := by
            simp only [mul_neg, neg_mul]
      _ = -(((gamma b * gamma a) * gamma c) * gamma b) := by
            simp only [mul_assoc]
      _ = -(((-(gamma a * gamma b)) * gamma c) * gamma b) := by
            rw [source9OriginalGamma_anticommute b a hba]
      _ = ((gamma a * gamma b) * gamma c) * gamma b := by
            simp only [neg_mul, neg_neg]
      _ = (gamma a * (gamma b * gamma c)) * gamma b := by
            simp only [mul_assoc]
      _ = (gamma a * (-(gamma c * gamma b))) * gamma b := by
            rw [source9OriginalGamma_anticommute b c hbc]
      _ = -((gamma a * gamma c) * (gamma b * gamma b)) := by
            simp only [mul_neg, neg_mul, mul_assoc]
      _ = -(gamma a * gamma c) := by
            rw [source9OriginalGamma_basis_mul_self b, mul_one]
  rw [hforward, hreverse]
  simp only [sub_neg_eq_add, two_smul]

/-- Same exact chain bracket in native so(16,R),
now for ANY distinct a,b,c without orientation
assumptions or private signed-permutation tables. -/
theorem source9OriginalGamma_distinct_chain_native_so_bracket
    (a b c : SpaceIndex)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ⁅source9OriginalGammaDistinctPairInSo a b hab,
      source9OriginalGammaDistinctPairInSo b c hbc⁆ =
      (2 : ℝ) • source9OriginalGammaDistinctPairInSo a c hac := by
  apply Subtype.ext
  change (gamma a * gamma b) * (gamma b * gamma c) -
    (gamma b * gamma c) * (gamma a * gamma b) =
      (2 : ℝ) • (gamma a * gamma c)
  exact source9OriginalGamma_distinct_chain_matrix_commutator
    a b c hab hac hbc

#print axioms source9OriginalGamma_distinct_pair_transpose_neg
#print axioms source9OriginalGamma_distinct_pair_mem_so
#print axioms source9OriginalGamma_distinct_pair_reverse_sign
#print axioms source9OriginalGamma_distinct_pair_agrees_ordered
#print axioms source9OriginalGamma_distinct_chain_matrix_commutator
#print axioms source9OriginalGamma_distinct_chain_native_so_bracket

end
end FCP.BFSSPairedSpin9Clifford
