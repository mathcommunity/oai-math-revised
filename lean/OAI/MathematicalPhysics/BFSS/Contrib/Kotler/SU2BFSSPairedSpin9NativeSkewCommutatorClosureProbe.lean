import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9NativeSkewCommutatorEqualityProbe

/-!
K1D18V9O — exact native source skew-matrix commutator closure.

V9N qualified the original paired-Fock 48-real coefficient map
preserving real 9×9 matrix product commutators for skew inputs.
This stage independently proves that the actual source matrix
commutator belongs to the source skew carrier.

The skew-carrier LieAlgebra and LieHom constructions, global Spin(9)
integration and BFSS physical/spectral claims remain separate.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0

/-- The actual native matrix commutator of two real skew nine-index
matrices is again skew, including all index coincidences. -/
theorem coordinateSkewMatrix9_commutator_closed
    (A B : Matrix SpaceIndex SpaceIndex ℝ)
    (hA : A.transpose = -A)
    (hB : B.transpose = -B) :
    (A * B - B * A).transpose = -(A * B - B * A) := by
  calc
    (A * B - B * A).transpose =
        B.transpose * A.transpose - A.transpose * B.transpose := by
      rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul]
    _ = -(A * B - B * A) := by
      rw [hA, hB]
      simp only [neg_mul, mul_neg, neg_neg, neg_sub]

#print axioms coordinateSkewMatrix9_commutator_closed

end
end FCP.BFSSPairedSpin9Plane
