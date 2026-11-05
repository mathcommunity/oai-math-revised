import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7GOriginalSourceNativeEuclideanReflectionCorrespondenceProbe
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Span.Defs

/-!
K1D18V7H — native hyperplane reflection unit-normal / zero split.

Source-exact successor to independently accepted V7G.
Pinned Mathlib's Cartan–Dieudonné theorem gives a list of arbitrary
Euclidean hyperplane reflection normals; it does NOT promise that
every listed vector is nonzero or normalized. This finite-dimensional
auxiliary lemma isolates that missing type-level interface.

For zero normal, the native hyperplane reflection is identity.
For nonzero normal, multiplication by the inverse norm yields a unit
vector spanning the SAME real line, hence the SAME hyperplane and
the SAME native hyperplane reflection.

No original 48-label basis reordering, substitute quadratic form,
Spin generation assumption, determinant parity conclusion,
global Spin9 lift, covering or physical BFSS claim is introduced.
No claim that the arbitrary Cartan factorization already has even
length or can be directly mapped to sourceSO without additional work.
All roots are CANDIDATES pending strict independent CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V7H
noncomputable section
open FCP.BFSSS1V0
open Submodule

private abbrev Euc48 := EuclideanSpace ℝ Source48Label

/-- Unit-normal choice for any nonzero native Euclidean normal. -/
noncomputable def euclideanUnitNormal (u : Euc48) : Euc48 :=
  (‖u‖ : ℝ)⁻¹ • u

/-- The unit normal has norm one; the hypothesis excludes the
zero normal and is required for cancellation. -/
theorem euclideanUnitNormal_norm_one
    (u : Euc48) (hu : u ≠ 0) :
    ‖euclideanUnitNormal u‖ = 1 := by
  have hnorm : ‖u‖ ≠ 0 := (norm_ne_zero_iff).2 hu
  calc
    ‖euclideanUnitNormal u‖ = ‖(‖u‖ : ℝ)⁻¹‖ * ‖u‖ := by
      rw [euclideanUnitNormal, norm_smul]
    _ = (‖u‖ : ℝ)⁻¹ * ‖u‖ := by
      rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg u)]
    _ = 1 := inv_mul_cancel₀ hnorm

/-- Nonzero normalization DOES NOT CHANGE the native real line,
so the orthogonal hyperplane is unchanged as well. -/
theorem euclideanUnitNormal_span_eq
    (u : Euc48) (hu : u ≠ 0) :
    (ℝ ∙ euclideanUnitNormal u) = (ℝ ∙ u) := by
  have hnorm : ‖u‖ ≠ 0 := (norm_ne_zero_iff).2 hu
  have hunit : IsUnit ((‖u‖ : ℝ)⁻¹) :=
    isUnit_iff_ne_zero.mpr (inv_ne_zero hnorm)
  change (ℝ ∙ ((‖u‖ : ℝ)⁻¹ • u)) = (ℝ ∙ u)
  exact Submodule.span_singleton_smul_eq hunit u

/-- The pinned native hyperplane-reflection map is literally
unchanged by the above normalization. -/
theorem euclideanUnitNormal_reflection_eq
    (u : Euc48) (hu : u ≠ 0) :
    (ℝ ∙ euclideanUnitNormal u)ᗮ.reflection = (ℝ ∙ u)ᗮ.reflection := by
  simp only [euclideanUnitNormal_span_eq u hu]

/-- A zero-normal native HYPERPLANE reflection is the identity;
crucial for discarding zero factors before determinant parity.
This is not the native LINE reflection, which would negate. -/
theorem euclideanHyperplaneReflection_zero :
    (ℝ ∙ (0 : Euc48))ᗮ.reflection = 1 := by
  ext w
  rw [Submodule.reflection_orthogonal_apply,
      Submodule.reflection_singleton_apply]
  simp

/-- Exact binary case needed after Cartan–Dieudonné:
each native hyperplane factor either has a nonzero unit-normal
representative, or is truly the identity if its normal was zero. -/
theorem euclideanHyperplaneReflection_unitOrIdentity
    (u : Euc48) :
    (∃ v : Euc48, ‖v‖ = 1 ∧
      (ℝ ∙ u)ᗮ.reflection = (ℝ ∙ v)ᗮ.reflection) ∨
      (ℝ ∙ u)ᗮ.reflection = 1 := by
  by_cases hu : u = 0
  · right
    subst u
    exact euclideanHyperplaneReflection_zero
  · left
    refine ⟨euclideanUnitNormal u, euclideanUnitNormal_norm_one u hu, ?_⟩
    exact (euclideanUnitNormal_reflection_eq u hu).symm

#print axioms euclideanUnitNormal
#print axioms euclideanUnitNormal_norm_one
#print axioms euclideanUnitNormal_span_eq
#print axioms euclideanUnitNormal_reflection_eq
#print axioms euclideanHyperplaneReflection_zero
#print axioms euclideanHyperplaneReflection_unitOrIdentity

end
end FCP.BFSSS1V52K1D18V7H
