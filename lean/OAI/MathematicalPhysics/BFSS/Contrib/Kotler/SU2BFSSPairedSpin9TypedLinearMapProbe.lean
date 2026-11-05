import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9FiniteCoefficientScalarProbe

/-!
K1D18V8Z — source-exact typed real LinearMap between the native
nine-index input and original paired Fock 48-real output.

The field obligations are exactly the accepted V8X additivity
and V8Y real scalar-homogeneity theorems. No different basis,
index permutation, extra axioms, or new physical hypothesis.

Only the typed map and its exact evaluation are claimed. Agreement
with source-native F_rs generators, skew carrier membership,
arbitrary Lie bracket preservation and global Spin(9) lift remain
separate unproved obligations.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0

/-- A genuine real linear map from native 9×9 matrices to original
48-real Fock-paired matrices, using the previously verified fields. -/
noncomputable def coordinateToPairedLinearMap :
    Matrix SpaceIndex SpaceIndex ℝ →ₗ[ℝ]
      Matrix Source48Label Source48Label ℝ where
  toFun := coordinateToPairedFiniteLift
  map_add' := coordinateToPairedFiniteLift_add
  map_smul' := coordinateToPairedFiniteLift_smul

/-- The typed LinearMap evaluates to precisely the accepted coefficient
sum, without a change of the original paired 48-real label order. -/
theorem coordinateToPairedLinearMap_apply
    (A : Matrix SpaceIndex SpaceIndex ℝ) :
    coordinateToPairedLinearMap A =
      coordinateToPairedFiniteLift A := by
  rfl

#print axioms coordinateToPairedLinearMap_apply

end
end FCP.BFSSPairedSpin9Plane
