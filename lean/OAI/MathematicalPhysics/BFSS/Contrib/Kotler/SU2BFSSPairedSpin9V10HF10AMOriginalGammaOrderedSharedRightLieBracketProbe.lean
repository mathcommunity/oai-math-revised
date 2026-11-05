import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10ALOriginalGammaOrderedForkLieBracketProbe

/-!
K1D18V10H-F10AM — ORIGINAL source gamma ordered
shared-RIGHT-index Lie bracket.

F10AK qualified the ordered chain bracket for a<b<c:
  [gamma_a gamma_b, gamma_b gamma_c] = 2 gamma_a gamma_c.
F10AL qualified the shared-LEFT-index fork bracket:
  [gamma_a gamma_b, gamma_a gamma_c] = -2 gamma_b gamma_c.

This gate tests the remaining distinct-three-index
overlap pattern, shared-RIGHT c:
  [gamma_a gamma_c, gamma_b gamma_c] = -2 gamma_a gamma_b.
The negative factor is derived from ORIGINAL source
gamma anticommutation and gamma_c squared = 1.
Its native Lie bracket is the exact Mathlib bracket
on the ACTUAL so(16,R) elements qualified by F10AJ.

All results are restricted to source indices a<b<c.
The four-distinct-index disjoint bracket, complete native
so(9) source basis and LieHom remain OPEN.
No 256-word even Clifford independence, faithful even
Clifford AlgHom, global Spin9/Spin48 lift, Fock action,
BFSS spectral or other physical result follows from this.

CANDIDATE pending source pinned -DwarningAsError=true
Lean and four independent exact type/root-axiom audits.
No private gamma tables, replacement matrices, axioms,
sorry, weakened hypotheses or resource-limit escalation.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9DetFixture
open OAI.BFSSQuantum
open Matrix

/-- The original gamma a-c / b-c product is -gamma a-b
for distinct canonically ordered source labels a<b<c. -/
theorem source9OriginalGamma_ordered_shared_right_forward_product
    (a b c : SpaceIndex) (_hab : a < b) (hbc : b < c) :
    (gamma a * gamma c) * (gamma b * gamma c) =
      -(gamma a * gamma b) := by
  have hcb : c ≠ b := ne_of_gt hbc
  calc
    (gamma a * gamma c) * (gamma b * gamma c) =
        (gamma a * (gamma c * gamma b)) * gamma c := by
          simp only [mul_assoc]
    _ = (gamma a * (-(gamma b * gamma c))) * gamma c := by
          rw [source9OriginalGamma_anticommute c b hcb]
    _ = -((gamma a * gamma b) * (gamma c * gamma c)) := by
          simp only [mul_neg, neg_mul, mul_assoc]
    _ = -(gamma a * gamma b) := by
          rw [source9OriginalGamma_basis_mul_self c, mul_one]

/-- The reverse original source pair product equals
positive gamma a-b, without private gamma-table lookup. -/
theorem source9OriginalGamma_ordered_shared_right_reverse_product
    (a b c : SpaceIndex) (hab : a < b) (hbc : b < c) :
    (gamma b * gamma c) * (gamma a * gamma c) =
      gamma a * gamma b := by
  have hca : c ≠ a := ne_of_gt (hab.trans hbc)
  have hba : b ≠ a := ne_of_gt hab
  calc
    (gamma b * gamma c) * (gamma a * gamma c) =
        (gamma b * (gamma c * gamma a)) * gamma c := by
          simp only [mul_assoc]
    _ = (gamma b * (-(gamma a * gamma c))) * gamma c := by
          rw [source9OriginalGamma_anticommute c a hca]
    _ = -((gamma b * gamma a) * (gamma c * gamma c)) := by
          simp only [mul_neg, neg_mul, mul_assoc]
    _ = -(gamma b * gamma a) := by
          rw [source9OriginalGamma_basis_mul_self c, mul_one]
    _ = gamma a * gamma b := by
          simp only [source9OriginalGamma_anticommute b a hba, neg_neg]

/-- Exact ORIGINAL real-matrix commutator for a<b<c
of two canonically ordered source gamma pairs with
shared RIGHT label c. -/
theorem source9OriginalGamma_ordered_shared_right_matrix_commutator
    (a b c : SpaceIndex) (hab : a < b) (hbc : b < c) :
    (gamma a * gamma c) * (gamma b * gamma c) -
      (gamma b * gamma c) * (gamma a * gamma c) =
        -((2 : ℝ) • (gamma a * gamma b)) := by
  rw [source9OriginalGamma_ordered_shared_right_forward_product
        a b c hab hbc,
      source9OriginalGamma_ordered_shared_right_reverse_product
        a b c hab hbc]
  simp only [two_smul]
  abel

/-- The same identity inside Mathlib's NATIVE orthogonal
LieSubalgebra of 16-by-16 real matrices. This is not yet
a full source so(9) LieHom. -/
theorem source9OriginalGamma_ordered_shared_right_native_so_bracket
    (a b c : SpaceIndex) (hab : a < b) (hbc : b < c) :
    ⁅source9OrderedGammaPairInSo ⟨(a,c),hab.trans hbc⟩,
      source9OrderedGammaPairInSo ⟨(b,c),hbc⟩⁆ =
      -((2 : ℝ) • source9OrderedGammaPairInSo ⟨(a,b),hab⟩) := by
  apply Subtype.ext
  change (gamma a * gamma c) * (gamma b * gamma c) -
    (gamma b * gamma c) * (gamma a * gamma c) =
      -((2 : ℝ) • (gamma a * gamma b))
  exact source9OriginalGamma_ordered_shared_right_matrix_commutator
    a b c hab hbc

#print axioms source9OriginalGamma_ordered_shared_right_forward_product
#print axioms source9OriginalGamma_ordered_shared_right_reverse_product
#print axioms source9OriginalGamma_ordered_shared_right_matrix_commutator
#print axioms source9OriginalGamma_ordered_shared_right_native_so_bracket

end
end FCP.BFSSPairedSpin9Clifford
