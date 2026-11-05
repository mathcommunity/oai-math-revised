import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10ANOriginalGammaDisjointPairLieBracketProbe

/-!
K1D18V10H-F10AO — native so(16,R) source gamma-pair
reversed-order and repeated-pair Lie-bracket completion.

Accepted F10AK/F10AL/F10AM each prove one oriented
three-distinct-index gamma-pair Lie bracket for any
a < b < c. Accepted F10AN proves the four-distinct
disjoint-pair bracket vanishes for any relative order.

Before claiming a full 36×36 ordered-pair bracket
table or native so(9)->so(16) LieHom, explicitly
qualify the reversed argument order for each of those
three nonzero families and the zero bracket for
identical pair arguments.

All four statements use the EXACT original gamma
product inside the preaccepted Mathlib native
LieAlgebra.Orthogonal.so SpinIndex ℝ, the pinned
mathlib lie_skew and lie_self properties, and the
source-exact qualified F10AK/F10AL/F10AM identities.

This module does not construct a LieHom or
formalize the complete arbitrary ordered-pair case
taxonomy. No original 256 even-Clifford gamma
basis injectivity, full Spin9/Spin48 lift, Fock
realization or BFSS physical conclusion is claimed.

No added axioms/sorry, resource increases or
substituted gamma representations. CANDIDATE until
frozen strict compiler and FOUR exact independent
declaration types/root-axiom checks PASS.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open OAI.BFSSQuantum
open Matrix

/-- Swapping the two source gamma pairs in F10AK
changes the chain bracket sign and retains the
original coefficient of exactly two. -/
theorem source9OriginalGamma_ordered_chain_reverse_native_so_bracket
    (a b c : SpaceIndex) (hab : a < b) (hbc : b < c) :
    ⁅source9OrderedGammaPairInSo ⟨(b,c),hbc⟩,
      source9OrderedGammaPairInSo ⟨(a,b),hab⟩⁆ =
      -((2 : ℝ) • source9OrderedGammaPairInSo
        ⟨(a,c),hab.trans hbc⟩) := by
  calc
    ⁅source9OrderedGammaPairInSo ⟨(b,c),hbc⟩,
        source9OrderedGammaPairInSo ⟨(a,b),hab⟩⁆ =
        -(-⁅source9OrderedGammaPairInSo ⟨(b,c),hbc⟩,
          source9OrderedGammaPairInSo ⟨(a,b),hab⟩⁆) := by
            simp only [neg_neg]
    _ = -⁅source9OrderedGammaPairInSo ⟨(a,b),hab⟩,
          source9OrderedGammaPairInSo ⟨(b,c),hbc⟩⁆ := by
            rw [lie_skew]
    _ = -((2 : ℝ) • source9OrderedGammaPairInSo
          ⟨(a,c),hab.trans hbc⟩) := by
            rw [source9OriginalGamma_ordered_chain_native_so_bracket
              a b c hab hbc]

/-- Reversed shared-left fork bracket: exact positive
two times the source gamma_b gamma_c matrix in
native so(16,R). -/
theorem source9OriginalGamma_ordered_fork_reverse_native_so_bracket
    (a b c : SpaceIndex) (hab : a < b) (hbc : b < c) :
    ⁅source9OrderedGammaPairInSo ⟨(a,c),hab.trans hbc⟩,
      source9OrderedGammaPairInSo ⟨(a,b),hab⟩⁆ =
      (2 : ℝ) • source9OrderedGammaPairInSo ⟨(b,c),hbc⟩ := by
  calc
    ⁅source9OrderedGammaPairInSo ⟨(a,c),hab.trans hbc⟩,
        source9OrderedGammaPairInSo ⟨(a,b),hab⟩⁆ =
        -(-⁅source9OrderedGammaPairInSo ⟨(a,c),hab.trans hbc⟩,
          source9OrderedGammaPairInSo ⟨(a,b),hab⟩⁆) := by
            simp only [neg_neg]
    _ = -⁅source9OrderedGammaPairInSo ⟨(a,b),hab⟩,
          source9OrderedGammaPairInSo ⟨(a,c),hab.trans hbc⟩⁆ := by
            rw [lie_skew]
    _ = -(-((2 : ℝ) • source9OrderedGammaPairInSo
          ⟨(b,c),hbc⟩)) := by
            rw [source9OriginalGamma_ordered_fork_native_so_bracket
              a b c hab hbc]
    _ = (2 : ℝ) • source9OrderedGammaPairInSo
          ⟨(b,c),hbc⟩ := by
            simp only [neg_neg]

/-- Reversed shared-right bracket: exact positive
two times original gamma_a gamma_b inside the
same native orthogonal LieSubalgebra. -/
theorem source9OriginalGamma_ordered_shared_right_reverse_native_so_bracket
    (a b c : SpaceIndex) (hab : a < b) (hbc : b < c) :
    ⁅source9OrderedGammaPairInSo ⟨(b,c),hbc⟩,
      source9OrderedGammaPairInSo ⟨(a,c),hab.trans hbc⟩⁆ =
      (2 : ℝ) • source9OrderedGammaPairInSo ⟨(a,b),hab⟩ := by
  calc
    ⁅source9OrderedGammaPairInSo ⟨(b,c),hbc⟩,
        source9OrderedGammaPairInSo ⟨(a,c),hab.trans hbc⟩⁆ =
        -(-⁅source9OrderedGammaPairInSo ⟨(b,c),hbc⟩,
          source9OrderedGammaPairInSo ⟨(a,c),hab.trans hbc⟩⁆) := by
            simp only [neg_neg]
    _ = -⁅source9OrderedGammaPairInSo ⟨(a,c),hab.trans hbc⟩,
          source9OrderedGammaPairInSo ⟨(b,c),hbc⟩⁆ := by
            rw [lie_skew]
    _ = -(-((2 : ℝ) • source9OrderedGammaPairInSo
          ⟨(a,b),hab⟩)) := by
            rw [source9OriginalGamma_ordered_shared_right_native_so_bracket
              a b c hab hbc]
    _ = (2 : ℝ) • source9OrderedGammaPairInSo
          ⟨(a,b),hab⟩ := by
            simp only [neg_neg]

/-- For EVERY one of the 36 actual canonical source
gamma pairs, its native so(16,R) self bracket is zero. -/
theorem source9OriginalGamma_ordered_pair_native_so_self_bracket_zero
    (p : Source9OrderedGammaPairIndex) :
    ⁅source9OrderedGammaPairInSo p,
      source9OrderedGammaPairInSo p⁆ =
      (0 : LieAlgebra.Orthogonal.so SpinIndex ℝ) := by
  exact lie_self _

#print axioms source9OriginalGamma_ordered_chain_reverse_native_so_bracket
#print axioms source9OriginalGamma_ordered_fork_reverse_native_so_bracket
#print axioms source9OriginalGamma_ordered_shared_right_reverse_native_so_bracket
#print axioms source9OriginalGamma_ordered_pair_native_so_self_bracket_zero

end
end FCP.BFSSPairedSpin9Clifford
