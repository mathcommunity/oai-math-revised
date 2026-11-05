import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9LieHomProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9LinearMapGeneratorAgreementProbe
import Mathlib.Algebra.Lie.SkewAdjoint

/-!
K1D18V9S — exact interface to Mathlib's real skew-adjoint
matrix Lie subalgebras and original normalized Spin(9) plane generators.

The accepted V9R LieHom is defined on the literal skew-transpose
subalgebras in native SpaceIndex and actual paired-Fock Source48Label.
Mathlib's skewAdjointMatricesLieSubalgebra (1 : Matrix n n ℝ) is the
canonical classical matrix Lie algebra interface. The source-index
and target-label equalities below are actual subtype equalities
obtained by spelling out the preserved transpose condition.

This does not construct smooth source groups or their Lie algebras
as tangent spaces, a group homomorphism, a Spin48 covering,
a Fock Hilbert-space operator, or a physical spectral theorem.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The V9R native real skew 9x9 carrier is exactly the pinned
Mathlib unit-form skew-adjoint matrix Lie subalgebra. -/
theorem coordinateSkewLieSubalgebra_eq_mathlib :
    coordinateSkewLieSubalgebra =
      skewAdjointMatricesLieSubalgebra
        (1 : Matrix SpaceIndex SpaceIndex ℝ) := by
  ext A
  change (A.transpose = -A) ↔
    A ∈ skewAdjointMatricesLieSubalgebra
      (1 : Matrix SpaceIndex SpaceIndex ℝ)
  rw [mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule]
  change (A.transpose = -A) ↔
    (A.transpose * (1 : Matrix SpaceIndex SpaceIndex ℝ) =
      (1 : Matrix SpaceIndex SpaceIndex ℝ) * (-A))
  simp only [mul_one, one_mul]

/-- The original 48-real Fock-paired skew carrier is also the
actual canonical Mathlib unit-form skew-adjoint Lie subalgebra,
with NO color-major substitution. -/
theorem pairedSkewLieSubalgebra_eq_mathlib :
    pairedSkewLieSubalgebra =
      skewAdjointMatricesLieSubalgebra
        (1 : Matrix Source48Label Source48Label ℝ) := by
  ext X
  change (X.transpose = -X) ↔
    X ∈ skewAdjointMatricesLieSubalgebra
      (1 : Matrix Source48Label Source48Label ℝ)
  rw [mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule]
  change (X.transpose = -X) ↔
    (X.transpose * (1 : Matrix Source48Label Source48Label ℝ) =
      (1 : Matrix Source48Label Source48Label ℝ) * (-X))
  simp only [mul_one, one_mul]

/-- The genuine native coordinate plane as an element of V9R's
input Lie algebra, including diagonal and reversed-index cases. -/
noncomputable def coordinatePlaneLie (r s : SpaceIndex) :
    coordinateSkewLieSubalgebra :=
  ⟨coordinatePlane9 r s, coordinatePlane9_transpose r s⟩

/-- The corresponding original Fock-paired normalized plane as
an element of V9R's output Lie algebra. -/
noncomputable def pairedPlaneLie (r s : SpaceIndex) :
    pairedSkewLieSubalgebra :=
  ⟨normalizedPairedPlane r s, normalizedPairedPlane_transpose r s⟩

/-- Exact generator-level identification within the TRUE typed LieHom,
not merely equality of unstructured 9x9 and 48x48 matrices. -/
theorem coordinateToPairedSkewLieHom_coordinatePlane (r s : SpaceIndex) :
    coordinateToPairedSkewLieHom (coordinatePlaneLie r s) =
      pairedPlaneLie r s := by
  apply Subtype.ext
  exact coordinateToPairedLinearMap_coordinatePlane r s

#print axioms coordinateSkewLieSubalgebra_eq_mathlib
#print axioms pairedSkewLieSubalgebra_eq_mathlib
#print axioms coordinateToPairedSkewLieHom_coordinatePlane

end
end FCP.BFSSPairedSpin9Plane
