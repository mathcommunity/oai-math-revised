import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9MathlibSkewBridgeProbe

/-!
K1D18V9T — a canonical Mathlib skew-adjoint LieHom interface.

The V9S source-exact carrier equalities identify the genuine V9R
native skew Lie homomorphism with the pinned standard unit-form
skew-adjoint Lie algebras, on the native SpaceIndex and original
Fock-paired Source48Label.

This is type-level transport of an already proven real LieHom.
It introduces no new gamma matrices, basis order, Lie bracket,
group integration, continuity, covering, or BFSS spectral claim.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Canonical pinned Mathlib real skew-adjoint Lie algebra map;
this is the accepted V9R LieHom transported through V9S carrier equalities. -/
noncomputable def coordinateToPairedCanonicalSkewLieHom :
    skewAdjointMatricesLieSubalgebra
        (1 : Matrix SpaceIndex SpaceIndex ℝ) →ₗ⁅ℝ⁆
      skewAdjointMatricesLieSubalgebra
        (1 : Matrix Source48Label Source48Label ℝ) := by
  rw [← coordinateSkewLieSubalgebra_eq_mathlib,
      ← pairedSkewLieSubalgebra_eq_mathlib]
  exact coordinateToPairedSkewLieHom

/-- Independent concrete bracket specialization on the standard Mathlib
carriers: the same original 9-to-paired-48 representation. -/
theorem coordinateToPairedCanonicalSkewLieHom_map_lie
    (A B : skewAdjointMatricesLieSubalgebra
      (1 : Matrix SpaceIndex SpaceIndex ℝ)) :
    coordinateToPairedCanonicalSkewLieHom ⁅A, B⁆ =
      ⁅coordinateToPairedCanonicalSkewLieHom A,
        coordinateToPairedCanonicalSkewLieHom B⁆ := by
  exact LieHom.map_lie coordinateToPairedCanonicalSkewLieHom A B

#print axioms coordinateToPairedCanonicalSkewLieHom
#print axioms coordinateToPairedCanonicalSkewLieHom_map_lie

end
end FCP.BFSSPairedSpin9Plane
