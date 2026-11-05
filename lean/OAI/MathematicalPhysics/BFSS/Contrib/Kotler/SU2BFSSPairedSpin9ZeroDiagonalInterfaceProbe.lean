import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9OrientationSwapProbe

/-!
K1D18V8H — zero-diagonal, antisymmetric source-native paired Spin(9)
plane generator interface.

The source-defined doubled plane K(r,s) = reindex(1 ⊗ₖ -(gamma r * gamma s))
has a nonzero diagonal (indeed K(r,r) = -I). One must NOT blindly use K
as an all-pairs so(9) basis with the expected diagonal-zero convention.

Define L(r,s) = 0 when r=s, otherwise exactly K(r,s), on the original
Source48Label. The three following results establish the source-EXACT
diagonal, off-diagonal and orientation bridges. This is a typed matrix
interface, not a Lie representation, group action or BFSS spectral claim.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0

/-- A zero-diagonal orientation-sensitive plane matrix on the actual original
Fock paired 48-real labels. Its off-diagonal value is EXACTLY V8A's K. -/
noncomputable def zeroDiagonalPairedPlane (r s : SpaceIndex) :
    Matrix Source48Label Source48Label ℝ :=
  if r = s then 0 else originalPairedPlane r s

/-- The all-pairs Lie-basis interface vanishes on the diagonal, unlike raw K. -/
theorem zeroDiagonalPairedPlane_self (r : SpaceIndex) :
    zeroDiagonalPairedPlane r r = 0 := by
  simp [zeroDiagonalPairedPlane]

/-- Off diagonal, the interface is the *unchanged* original paired K matrix. -/
theorem zeroDiagonalPairedPlane_of_ne (r s : SpaceIndex) (hrs : r ≠ s) :
    zeroDiagonalPairedPlane r s = originalPairedPlane r s := by
  simp [zeroDiagonalPairedPlane, hrs]

/-- All-pairs orientation antisymmetry, including the diagonal boundary. -/
theorem zeroDiagonalPairedPlane_swap (r s : SpaceIndex) :
    zeroDiagonalPairedPlane s r = -(zeroDiagonalPairedPlane r s) := by
  by_cases hrs : r = s
  · subst s
    simp [zeroDiagonalPairedPlane]
  · have hsr : s ≠ r := Ne.symm hrs
    rw [zeroDiagonalPairedPlane_of_ne s r hsr,
      zeroDiagonalPairedPlane_of_ne r s hrs]
    exact originalPairedPlane_swap_order r s hrs

#print axioms zeroDiagonalPairedPlane_self
#print axioms zeroDiagonalPairedPlane_of_ne
#print axioms zeroDiagonalPairedPlane_swap

end
end FCP.BFSSPairedSpin9Plane
