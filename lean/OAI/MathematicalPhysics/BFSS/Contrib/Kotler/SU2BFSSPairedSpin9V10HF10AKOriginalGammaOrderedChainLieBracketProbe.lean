import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10AJOriginalGammaPairOrthogonalLieSubalgebraBridge

/-!
K1D18V10H-F10AK — source ORIGINAL ordered gamma-pair
Lie bracket, an essential prerequisite for an actual
so(9) → so(16) LieHom.

F10AJ qualified that all 36 original gamma-pair words
live in Mathlib's native so(16,R) Lie subalgebra and are
linearly independent there. This gate computes one exact
nontrivial bracket family, for any a<b<c.

No new gamma representation or private signed-permutation
tables. We use only the accepted public Clifford relations
of the original nine symmetric 16-real gamma matrices,
including gamma_b²=1 and all distinct anticommutation.

The tested source identity is
    [gamma_a gamma_b, gamma_b gamma_c] = 2 gamma_a gamma_c.
The factor 2 is from the ACTUAL matrix commutator bracket
in Mathlib, not a freely chosen spin-Lie normalization.

This is NOT yet a globally defined LieHom from the native
so(9) basis and does not show all bracket cases. It proves
no group-level Spin9/Spin48 lift, 256 even Clifford-word
independence, full Clifford injection, Fock representation,
or BFSS physics. Preserve exact source-label ordering.

CANDIDATE pending frozen strict Lean warning-as-error
compilation, all three independently elaborated declaration
types and declaration-level root axiom audits.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9DetFixture
open OAI.BFSSQuantum
open Matrix

/-- The reverse of the adjacent ordered gamma-pair word
product is minus the original gamma_a gamma_c, whenever
the ORIGINAL source labels satisfy a<b<c. -/
theorem source9OriginalGamma_ordered_chain_reverse_product
    (a b c : SpaceIndex) (hab : a < b) (hbc : b < c) :
    (gamma b * gamma c) * (gamma a * gamma b) =
      -(gamma a * gamma c) := by
  have hca : c ≠ a := ne_of_gt (hab.trans hbc)
  have hba : b ≠ a := ne_of_gt hab
  have hbc' : b ≠ c := ne_of_lt hbc
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
          rw [source9OriginalGamma_anticommute b c hbc']
    _ = -((gamma a * gamma c) * (gamma b * gamma b)) := by
          simp only [mul_neg, neg_mul, mul_assoc]
    _ = -(gamma a * gamma c) := by
          rw [source9OriginalGamma_basis_mul_self b, mul_one]

/-- Exact nontrivial matrix commutator of the original
16-real public gamma pair words for any a<b<c.
This is an associative ring subtraction identity. -/
theorem source9OriginalGamma_ordered_chain_matrix_commutator
    (a b c : SpaceIndex) (hab : a < b) (hbc : b < c) :
    (gamma a * gamma b) * (gamma b * gamma c) -
      (gamma b * gamma c) * (gamma a * gamma b) =
        (2 : ℝ) • (gamma a * gamma c) := by
  have hforward :
      (gamma a * gamma b) * (gamma b * gamma c) =
        gamma a * gamma c := by
    calc
      (gamma a * gamma b) * (gamma b * gamma c) =
          gamma a * ((gamma b * gamma b) * gamma c) := by
            simp only [mul_assoc]
      _ = gamma a * gamma c := by
            rw [source9OriginalGamma_basis_mul_self b, one_mul]
  rw [hforward,
      source9OriginalGamma_ordered_chain_reverse_product a b c hab hbc]
  simp only [sub_neg_eq_add, two_smul]

/-- The SAME original a<b<c bracket identity INSIDE
Mathlib's NATIVE so(16,R), whose Lie bracket is the
underlying matrix commutator. This is the first exact
nonzero bracket compatibility needed before a source
so(9) LieHom can be constructed. -/
theorem source9OriginalGamma_ordered_chain_native_so_bracket
    (a b c : SpaceIndex) (hab : a < b) (hbc : b < c) :
    ⁅source9OrderedGammaPairInSo ⟨(a,b),hab⟩,
      source9OrderedGammaPairInSo ⟨(b,c),hbc⟩⁆ =
      (2 : ℝ) • source9OrderedGammaPairInSo
        ⟨(a,c),hab.trans hbc⟩ := by
  apply Subtype.ext
  change (gamma a * gamma b) * (gamma b * gamma c) -
    (gamma b * gamma c) * (gamma a * gamma b) =
      (2 : ℝ) • (gamma a * gamma c)
  exact source9OriginalGamma_ordered_chain_matrix_commutator
    a b c hab hbc

#print axioms source9OriginalGamma_ordered_chain_reverse_product
#print axioms source9OriginalGamma_ordered_chain_matrix_commutator
#print axioms source9OriginalGamma_ordered_chain_native_so_bracket

end
end FCP.BFSSPairedSpin9Clifford
