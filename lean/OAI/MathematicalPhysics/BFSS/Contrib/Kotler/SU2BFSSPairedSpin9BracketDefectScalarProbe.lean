import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9BracketDefectAdditivityProbe

/-!
K1D18V9J — real scalar homogeneity of both arguments of the
exact source-native bracket preservation defect.

V9I strictly proved its additivity in each argument. This
stage completes the two separate ℝ-homogeneity obligations,
using native Matrix SpaceIndex SpaceIndex ℝ multiplication,
the accepted typed real coefficient LinearMap, and original
paired-Fock Source48Label output matrix multiplication.

No skew hypothesis is imposed. Arbitrary skew-input
commutator preservation, typed LieHom, global Spin(9) integration
and BFSS physical conclusions remain separate obligations.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0

/-- Real homogeneity of the exact commutator defect in its
first source-native nine-index matrix argument. -/
theorem coordinateToPairedBracketDefect_smul_left
    (c : ℝ) (A B : Matrix SpaceIndex SpaceIndex ℝ) :
    coordinateToPairedBracketDefect (c • A) B =
      c • coordinateToPairedBracketDefect A B := by
  unfold coordinateToPairedBracketDefect
  simp only [smul_mul_assoc, mul_smul_comm,
    map_smul, map_sub, smul_sub]

/-- Real homogeneity of the exact commutator defect in its
second source-native nine-index matrix argument. -/
theorem coordinateToPairedBracketDefect_smul_right
    (c : ℝ) (A B : Matrix SpaceIndex SpaceIndex ℝ) :
    coordinateToPairedBracketDefect A (c • B) =
      c • coordinateToPairedBracketDefect A B := by
  unfold coordinateToPairedBracketDefect
  simp only [smul_mul_assoc, mul_smul_comm,
    map_smul, map_sub, smul_sub]

#print axioms coordinateToPairedBracketDefect_smul_left
#print axioms coordinateToPairedBracketDefect_smul_right

end
end FCP.BFSSPairedSpin9Plane
