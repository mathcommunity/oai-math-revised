import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9LinearMapGeneratorAgreementProbe

/-!
K1D18V9C — exact original paired 48-real skew-matrix image of the
source-native 9×9 to 48×48 coefficient LinearMap.

Every original normalized output generator H_rs is skew on the
Fock-paired source label basis. Any real linear combination remains
skew, including the image of arbitrary 9×9 A (not merely skew A).

This is a transpose identity, not yet a typed so(9) → so(48)
Lie algebra homomorphism; arbitrary bracket preservation, global
Spin(9) lift, and BFSS physical claims remain separate.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open scoped BigOperators

/-- Every value of the original paired-Fock coefficient map is
skew-symmetric on its full source-exact 48-real output labels. -/
theorem coordinateToPairedLinearMap_image_transpose
    (A : Matrix SpaceIndex SpaceIndex ℝ) :
    (coordinateToPairedLinearMap A).transpose =
      -(coordinateToPairedLinearMap A) := by
  rw [coordinateToPairedLinearMap_apply]
  simp only [coordinateToPairedFiniteLift, Matrix.transpose_smul,
    Matrix.transpose_sum, normalizedPairedPlane_transpose,
    smul_neg, Finset.sum_neg_distrib]

#print axioms coordinateToPairedLinearMap_image_transpose

end
end FCP.BFSSPairedSpin9Plane
