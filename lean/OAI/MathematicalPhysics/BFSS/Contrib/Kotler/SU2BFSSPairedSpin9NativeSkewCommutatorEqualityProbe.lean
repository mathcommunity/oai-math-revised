import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9BracketDefectSkewPairVanishingProbe

/-!
K1D18V9N — exact direct source-native arbitrary skew matrix
commutator-preservation statement for the original paired-Fock
48-real coefficient LinearMap.

V9M already qualified the zero defect for any skew 9×9 input
pair. This bounded typed bridge extracts the original actual
matrix multiplication identity explicitly, without hiding it
behind a defined defect or assuming a LieHom.

Constructing the input/output skew Lie algebra carriers, a
typed LieHom, global Spin(9) integration and BFSS physical
existence are separate obligations.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0

/-- Exact original source-native real skew 9×9 to paired-Fock
48-real matrix product commutator preservation. -/
theorem coordinateToPairedLinearMap_skew_commutator
    (A B : Matrix SpaceIndex SpaceIndex ℝ)
    (hA : A.transpose = -A)
    (hB : B.transpose = -B) :
    coordinateToPairedLinearMap (A * B - B * A) =
      coordinateToPairedLinearMap A * coordinateToPairedLinearMap B -
      coordinateToPairedLinearMap B * coordinateToPairedLinearMap A := by
  have h := coordinateToPairedBracketDefect_skew_pair_zero A B hA hB
  change
    coordinateToPairedLinearMap (A * B - B * A) -
      (coordinateToPairedLinearMap A * coordinateToPairedLinearMap B -
       coordinateToPairedLinearMap B * coordinateToPairedLinearMap A) = 0 at h
  exact sub_eq_zero.mp h

#print axioms coordinateToPairedLinearMap_skew_commutator

end
end FCP.BFSSPairedSpin9Plane
