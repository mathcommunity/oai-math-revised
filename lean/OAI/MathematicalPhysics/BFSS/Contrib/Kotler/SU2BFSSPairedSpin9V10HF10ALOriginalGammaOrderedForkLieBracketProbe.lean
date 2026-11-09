import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10AKOriginalGammaOrderedChainLieBracketProbe

/-!
K1D18V10H-F10AL — ORIGINAL source gamma ordered-fork Lie bracket.

F10AK qualified the ordered-chain native so(16,R) bracket
  [gamma_a gamma_b, gamma_b gamma_c] = 2 gamma_a gamma_c
for a < b < c.

This bounded follow-on tests the distinct shared-LEFT-index
fork case for the SAME source gamma pair representatives:
  [gamma_a gamma_b, gamma_a gamma_c] = -2 gamma_b gamma_c.
The negative sign and normalization are derived directly
from ORIGINAL public source Clifford anticommutation and
gamma_a squared equals 1, not from a guessed so(9) map.

Prove both ordered product directions and the commutator as
actual sixteen-real matrices, then lift the verified bracket
identity to Mathlib's native so(16,R) LieSubalgebra.

No LieHom so(9) -> so(16) is asserted here: shared-right
and disjoint-index brackets plus a source-defined native
so(9) basis bridge remain separate obligations. The full
256 even gamma-image basis, original even Clifford map
injectivity, global Spin group lifts, Fock and BFSS physics
also remain unproved.

CANDIDATE until source-pinned warnings-as-errors Lean and
FOUR independently elaborated declarations/axioms pass.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9DetFixture
open OAI.BFSSQuantum
open Matrix

/-- The forward fork source product AB*AC is -BC for
the exact original symmetric real gamma matrices. -/
theorem source9OriginalGamma_ordered_fork_forward_product
    (a b c : SpaceIndex) (hab : a < b) (_hbc : b < c) :
    (gamma a * gamma b) * (gamma a * gamma c) =
      -(gamma b * gamma c) := by
  have hba : b ≠ a := ne_of_gt hab
  calc
    (gamma a * gamma b) * (gamma a * gamma c) =
        (gamma a * (gamma b * gamma a)) * gamma c := by
          simp only [mul_assoc]
    _ = (gamma a * (-(gamma a * gamma b))) * gamma c := by
          rw [source9OriginalGamma_anticommute b a hba]
    _ = -((gamma a * gamma a) * (gamma b * gamma c)) := by
          simp only [mul_neg, neg_mul, mul_assoc]
    _ = -(gamma b * gamma c) := by
          rw [source9OriginalGamma_basis_mul_self a, one_mul]

/-- The reversed fork AC*AB equals +BC after three
original gamma-factor moves and gamma_a squared equals 1. -/
theorem source9OriginalGamma_ordered_fork_reverse_product
    (a b c : SpaceIndex) (hab : a < b) (hbc : b < c) :
    (gamma a * gamma c) * (gamma a * gamma b) =
      gamma b * gamma c := by
  have hca : c ≠ a := ne_of_gt (hab.trans hbc)
  have hcb : c ≠ b := ne_of_gt hbc
  calc
    (gamma a * gamma c) * (gamma a * gamma b) =
        (gamma a * (gamma c * gamma a)) * gamma b := by
          simp only [mul_assoc]
    _ = (gamma a * (-(gamma a * gamma c))) * gamma b := by
          rw [source9OriginalGamma_anticommute c a hca]
    _ = -((gamma a * gamma a) * (gamma c * gamma b)) := by
          simp only [mul_neg, neg_mul, mul_assoc]
    _ = -(gamma c * gamma b) := by
          rw [source9OriginalGamma_basis_mul_self a, one_mul]
    _ = gamma b * gamma c := by
          simp only [source9OriginalGamma_anticommute c b hcb, neg_neg]

/-- The exact source gamma matrix commutator has
coefficient NEGATIVE TWO for a<b<c and shared left a. -/
theorem source9OriginalGamma_ordered_fork_matrix_commutator
    (a b c : SpaceIndex) (hab : a < b) (hbc : b < c) :
    (gamma a * gamma b) * (gamma a * gamma c) -
      (gamma a * gamma c) * (gamma a * gamma b) =
        -((2 : ℝ) • (gamma b * gamma c)) := by
  rw [source9OriginalGamma_ordered_fork_forward_product a b c hab hbc,
      source9OriginalGamma_ordered_fork_reverse_product a b c hab hbc]
  simp only [two_smul]
  abel

/-- The SAME nontrivial fork bracket inside the native
Mathlib orthogonal LieSubalgebra of 16-real matrices.
This is NOT a full native source so(9) LieHom. -/
theorem source9OriginalGamma_ordered_fork_native_so_bracket
    (a b c : SpaceIndex) (hab : a < b) (hbc : b < c) :
    ⁅source9OrderedGammaPairInSo ⟨(a,b),hab⟩,
      source9OrderedGammaPairInSo ⟨(a,c),hab.trans hbc⟩⁆ =
      -((2 : ℝ) • source9OrderedGammaPairInSo ⟨(b,c),hbc⟩) := by
  apply Subtype.ext
  change (gamma a * gamma b) * (gamma a * gamma c) -
    (gamma a * gamma c) * (gamma a * gamma b) =
      -((2 : ℝ) • (gamma b * gamma c))
  exact source9OriginalGamma_ordered_fork_matrix_commutator
    a b c hab hbc

#print axioms source9OriginalGamma_ordered_fork_forward_product
#print axioms source9OriginalGamma_ordered_fork_reverse_product
#print axioms source9OriginalGamma_ordered_fork_matrix_commutator
#print axioms source9OriginalGamma_ordered_fork_native_so_bracket

end
end FCP.BFSSPairedSpin9Clifford
