import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9UniversalFourIndexBracketProbe

/-!
K1D18V8N — source-exact original Fock-paired so(48) candidate carrier.

The all-indices L bracket was accepted in V8M on the actual Source48Label.
Here we transport the accepted V8A original K transpose and square results
across the exact V8H zero-diagonal interface.

Each L_rs is skew-symmetric even when r=s. If r≠s its square is -I.
No assertion of an abstract Lie algebra homomorphism, group integration,
Fock-space operator action or BFSS physics is made.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0

/-- Every zero-diagonal original paired 48-real plane is skew-symmetric. -/
theorem zeroDiagonalPairedPlane_transpose (r s : SpaceIndex) :
    (zeroDiagonalPairedPlane r s).transpose =
      -(zeroDiagonalPairedPlane r s) := by
  by_cases hrs : r = s
  · subst s
    simp [zeroDiagonalPairedPlane_self]
  · rw [zeroDiagonalPairedPlane_of_ne r s hrs]
    exact originalPairedPlane_transpose r s hrs

/-- Off-diagonal planes retain the exact original squared -I identity. -/
theorem zeroDiagonalPairedPlane_sq (r s : SpaceIndex) (hrs : r ≠ s) :
    zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane r s =
      -(1 : Matrix Source48Label Source48Label ℝ) := by
  rw [zeroDiagonalPairedPlane_of_ne r s hrs]
  exact originalPairedPlane_sq r s hrs

#print axioms zeroDiagonalPairedPlane_transpose
#print axioms zeroDiagonalPairedPlane_sq

end
end FCP.BFSSPairedSpin9Plane
