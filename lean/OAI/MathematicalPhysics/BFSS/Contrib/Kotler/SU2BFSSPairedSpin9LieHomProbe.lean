import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9TypedSkewCarrierLinearStructureProbe
import Mathlib.Algebra.Lie.OfAssociative

/-!
K1D18V9R — genuine source-native skew matrix Lie subalgebra to
exact original Fock-paired 48-real skew matrix Lie subalgebra homomorphism.

The input and target are the actual skew subalgebras of the full
matrix associative algebras with their genuine commutator brackets.
The coefficient map is the accepted V8Z real LinearMap, its source
Fock-paired skew output is V9C, its arbitrary skew bracket identity
is V9N, and the explicit carrier add/smul laws are V9Q.

No replacement label ordering, surrogate bracket, unproved transport,
global Spin(9) group integration, topology or BFSS physical theorem.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0

-- The pinned associative matrix ring yields the actual commutator Lie ring.
attribute [local instance 100] LieRing.ofAssociativeRing

/-- Actual source nine-index skew matrices as a real Lie subalgebra. -/
noncomputable def coordinateSkewLieSubalgebra :
    LieSubalgebra ℝ (Matrix SpaceIndex SpaceIndex ℝ) where
  carrier := {A | A.transpose = -A}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    change A.transpose = -A at hA
    change B.transpose = -B at hB
    change (A + B).transpose = -(A + B)
    rw [Matrix.transpose_add, hA, hB, neg_add]
  smul_mem' := by
    intro c A hA
    change A.transpose = -A at hA
    change (c • A).transpose = -(c • A)
    rw [Matrix.transpose_smul, hA, smul_neg]
  lie_mem' := by
    intro A B hA hB
    change (A * B - B * A).transpose = -(A * B - B * A)
    exact coordinateSkewMatrix9_commutator_closed A B hA hB

/-- Original paired-Fock source 48-label skew matrices as a real Lie subalgebra. -/
noncomputable def pairedSkewLieSubalgebra :
    LieSubalgebra ℝ (Matrix Source48Label Source48Label ℝ) where
  carrier := {X | X.transpose = -X}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    change X.transpose = -X at hX
    change Y.transpose = -Y at hY
    change (X + Y).transpose = -(X + Y)
    rw [Matrix.transpose_add, hX, hY, neg_add]
  smul_mem' := by
    intro c X hX
    change X.transpose = -X at hX
    change (c • X).transpose = -(c • X)
    rw [Matrix.transpose_smul, hX, smul_neg]
  lie_mem' := by
    intro X Y hX hY
    change (X * Y - Y * X).transpose = -(X * Y - Y * X)
    exact pairedSkewMatrix48_commutator_closed X Y hX hY

/-- The exact source-native 9-to-original-48 map is a genuine real LieHom
of the actual skew-matrix Lie subalgebras and commutator brackets. -/
noncomputable def coordinateToPairedSkewLieHom :
    coordinateSkewLieSubalgebra →ₗ⁅ℝ⁆ pairedSkewLieSubalgebra where
  toFun := fun A =>
    ⟨coordinateToPairedLinearMap A.val,
      coordinateToPairedLinearMap_image_transpose A.val⟩
  map_add' := by
    intro A B
    apply Subtype.ext
    change coordinateToPairedLinearMap (A.val + B.val) =
      coordinateToPairedLinearMap A.val + coordinateToPairedLinearMap B.val
    exact map_add coordinateToPairedLinearMap A.val B.val
  map_smul' := by
    intro c A
    apply Subtype.ext
    change coordinateToPairedLinearMap (c • A.val) =
      c • coordinateToPairedLinearMap A.val
    exact map_smul coordinateToPairedLinearMap c A.val
  map_lie' := by
    intro A B
    apply Subtype.ext
    change coordinateToPairedLinearMap (A.val * B.val - B.val * A.val) =
      coordinateToPairedLinearMap A.val * coordinateToPairedLinearMap B.val -
        coordinateToPairedLinearMap B.val * coordinateToPairedLinearMap A.val
    exact coordinateToPairedLinearMap_skew_commutator A.val B.val
      A.property B.property

#print axioms coordinateToPairedSkewLieHom

end
end FCP.BFSSPairedSpin9Plane
