import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7JNativeUnitHyperplaneDeterminantSignProbe
import Mathlib.LinearAlgebra.Determinant

/-!
K1D18V7K — actual native Euclidean isometry product determinant.

V7J is strictly accepted on the exact original 48-label Euclidean
coordinate type. Its unit-normal native hyperplane reflection has
real LinearMap determinant -1. V7I is strictly accepted: the actual
ordered Cartan factor list can be made unit-normal with zeros removed,
with no change to the product.

This next bounded candidate shows:
(1) determinant multiplicativity for the ACTUAL native
LinearIsometryEquiv group operation and associated LinearMap;
(2) determinant of the exact native unit-normal reflection list
product is (-1)^list.length, preserving Mathlib's list order.

No parity conclusion, even-list pairing, original sourceSO generator
membership or Spin48 image surjectivity is assumed or claimed.
No alternate original source Q, 48-label permutation or surrogate
matrix. All roots CANDIDATE until strict independent verification.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V7K
noncomputable section
open FCP.BFSSS1V0
open Submodule

private abbrev Euc48 := EuclideanSpace ℝ Source48Label

/-- The actual native group multiplication on Euclidean
LinearIsometryEquiv transports to composition of its actual
LinearMaps. Hence determinant is multiplicative. -/
theorem euclideanIsometry_mul_det
    (f g : Euc48 ≃ₗᵢ[ℝ] Euc48) :
    LinearMap.det ((f * g).toLinearMap) =
      LinearMap.det f.toLinearMap * LinearMap.det g.toLinearMap := by
  have hcomp : (f * g).toLinearMap = f.toLinearMap.comp g.toLinearMap := by
    ext x
    rfl
  rw [hcomp, LinearMap.det_comp]

/-- The ordered list of the ACTUAL native unit hyperplane
reflections has determinant (-1)^length, with no assumption
that the list has even length. This is the exact formula
needed before transporting original sourceSO determinant +1
and proving parity in a separate obligation. -/
theorem euclideanUnitReflectionList_det (l : List Euc48) :
    (∀ u ∈ l, ‖u‖ = 1) →
      LinearMap.det (((l.map fun u => (ℝ ∙ u)ᗮ.reflection).prod).toLinearMap) =
        (-1 : ℝ) ^ l.length := by
  induction l with
  | nil =>
      intro _
      change LinearMap.det (LinearMap.id : Euc48 →ₗ[ℝ] Euc48) = 1
      exact LinearMap.det_id
  | cons u tail ih =>
      intro hall
      have hu : ‖u‖ = 1 := hall u (by simp)
      have htail : ∀ v ∈ tail, ‖v‖ = 1 := by
        intro v hv
        exact hall v (by simp [hv])
      calc
        LinearMap.det ((((u :: tail).map fun v => (ℝ ∙ v)ᗮ.reflection).prod).toLinearMap) =
            LinearMap.det (((ℝ ∙ u)ᗮ.reflection *
              (tail.map fun v => (ℝ ∙ v)ᗮ.reflection).prod).toLinearMap) := by
              rfl
        _ = LinearMap.det ((ℝ ∙ u)ᗮ.reflection.toLinearMap) *
              LinearMap.det (((tail.map fun v => (ℝ ∙ v)ᗮ.reflection).prod).toLinearMap) :=
          euclideanIsometry_mul_det _ _
        _ = (-1 : ℝ) * (-1 : ℝ) ^ tail.length := by
          rw [FCP.BFSSS1V52K1D18V7J.euclideanUnitHyperplane_reflection_det_neg_one u hu,
            ih htail]
        _ = (-1 : ℝ) ^ (u :: tail).length := by
          simp only [List.length_cons, pow_succ]
          ring

#print axioms euclideanIsometry_mul_det
#print axioms euclideanUnitReflectionList_det

end
end FCP.BFSSS1V52K1D18V7K
