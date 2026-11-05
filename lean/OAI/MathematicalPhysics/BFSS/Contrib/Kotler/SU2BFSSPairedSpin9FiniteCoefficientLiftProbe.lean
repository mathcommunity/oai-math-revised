import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9CoordinateUniversalBracketProbe

/-!
K1D18V8X — first source-native finite-index coefficient lift from
9×9 real input matrices to original paired-Fock 48-real matrices.

Define the candidate rho(A) := (1/2) • sum_{r,s} A(r,s) • H_rs,
H_rs = -(1/2) • original zero-diagonal paired generator L_rs.
The input is precisely Matrix SpaceIndex SpaceIndex ℝ; the output
is precisely Matrix Source48Label Source48Label ℝ. No reindexing.

In this gate prove only rho(0)=0 and rho(A+B)=rho(A)+rho(B).
Scalar homogeneity, rho(F_rs)=H_rs, skew-carrier membership,
arbitrary Lie-bracket preservation and Spin(9) integration are
separate open obligations.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open scoped BigOperators

/-- Typed candidate coefficient map on native 9×9 real matrices.
The factor 1/2 is the ordered-pair normalization that must still
be checked against the accepted antisymmetric generators. -/
noncomputable def coordinateToPairedFiniteLift
    (A : Matrix SpaceIndex SpaceIndex ℝ) :
    Matrix Source48Label Source48Label ℝ :=
  (1 / 2 : ℝ) •
    ∑ r : SpaceIndex, ∑ s : SpaceIndex,
      (A r s) • normalizedPairedPlane r s

/-- The candidate sends the zero input matrix to zero. -/
theorem coordinateToPairedFiniteLift_zero :
    coordinateToPairedFiniteLift
      (0 : Matrix SpaceIndex SpaceIndex ℝ) = 0 := by
  simp [coordinateToPairedFiniteLift]

/-- The candidate preserves addition on arbitrary 9×9 matrices. -/
theorem coordinateToPairedFiniteLift_add
    (A B : Matrix SpaceIndex SpaceIndex ℝ) :
    coordinateToPairedFiniteLift (A + B) =
      coordinateToPairedFiniteLift A +
        coordinateToPairedFiniteLift B := by
  simp only [coordinateToPairedFiniteLift, Matrix.add_apply,
    add_smul, Finset.sum_add_distrib, smul_add]

#print axioms coordinateToPairedFiniteLift_zero
#print axioms coordinateToPairedFiniteLift_add

end
end FCP.BFSSPairedSpin9Plane
