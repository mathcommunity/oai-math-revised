import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9ZeroDiagonalSkewSquareProbe

/-!
K1D18V8O — explicitly normalized source-native 48-real Spin(9)
plane matrix interface, with no group or unproved Lie-hom assumption.

The accepted V8M doubled L brackets have the opposite sign and twice
the coefficient of the standard real so(9) generators E_rs - E_sr.
The required normalization is therefore H_rs := -(1/2) • L_rs.

Before proving a linear representation, establish H's typed diagonal,
antisymmetry and skew-matrix carrier on the exact source Fock-paired
Source48Label, using accepted V8H/V8N bridge roots. No limits raised.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0

/-- The minus-one-half normalized plane matrix on actual source 48 labels. -/
noncomputable def normalizedPairedPlane (r s : SpaceIndex) :
    Matrix Source48Label Source48Label ℝ :=
  (-(1 / 2 : ℝ)) • zeroDiagonalPairedPlane r s

/-- Normalization respects the zero diagonal, unlike raw original K. -/
theorem normalizedPairedPlane_self (r : SpaceIndex) :
    normalizedPairedPlane r r = 0 := by
  simp [normalizedPairedPlane, zeroDiagonalPairedPlane_self]

/-- Normalization respects antisymmetry even when indices coincide. -/
theorem normalizedPairedPlane_swap (r s : SpaceIndex) :
    normalizedPairedPlane s r = -(normalizedPairedPlane r s) := by
  change (-(1 / 2 : ℝ)) • zeroDiagonalPairedPlane s r =
    -((-(1 / 2 : ℝ)) • zeroDiagonalPairedPlane r s)
  rw [zeroDiagonalPairedPlane_swap r s, smul_neg]

/-- Every normalized source-original 48-real plane is skew-symmetric. -/
theorem normalizedPairedPlane_transpose (r s : SpaceIndex) :
    (normalizedPairedPlane r s).transpose = -(normalizedPairedPlane r s) := by
  simp only [normalizedPairedPlane]
  calc
    ((-(1 / 2 : ℝ)) • zeroDiagonalPairedPlane r s).transpose =
        (-(1 / 2 : ℝ)) • (zeroDiagonalPairedPlane r s).transpose := by
          ext i j
          rfl
    _ = -((-(1 / 2 : ℝ)) • zeroDiagonalPairedPlane r s) := by
          rw [zeroDiagonalPairedPlane_transpose, smul_neg]

#print axioms normalizedPairedPlane_self
#print axioms normalizedPairedPlane_swap
#print axioms normalizedPairedPlane_transpose

end
end FCP.BFSSPairedSpin9Plane
