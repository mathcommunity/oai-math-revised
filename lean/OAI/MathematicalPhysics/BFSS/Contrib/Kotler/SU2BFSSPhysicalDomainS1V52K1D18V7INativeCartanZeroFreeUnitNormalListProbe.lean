import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7HNativeHyperplaneUnitNormalOrIdentityProbe
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
K1D18V7I — zero-free Q-unit-compatible Euclidean Cartan normal list.

Source-exact successor to strictly accepted K1D18V7H:
- For each native Euclidean Cartan normal u=0 discard its TRUE
  identity hyperplane factor (not a minus-identity line reflection).
- For every u≠0 replace it by the accepted normalized unit normal
  preserving its ORIGINAL native hyperplane-reflection action.
- Track length and unit-normal invariants and prove equality of the
  entire ordered product, not merely individual factor equalities.
- Apply the accepted V7B pinned Cartan-Dieudonné list decomposition,
  obtaining an actual unit-normal factor list of length <= finrank 48.

The list is NOT yet known to have even length. This module does NOT
prove determinant parity, original-source Q-unit lifting,
surjectivity of sourceSO unit-pairs / Spin48 image, covering,
global Spin9 or BFSS spectra. No alternate source-Q form,
label reordering or original Clifford matrix changes.
All declarations CANDIDATES pending strict independent CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V7I
noncomputable section
open FCP.BFSSS1V0
open Submodule

private abbrev Euc48 := EuclideanSpace ℝ Source48Label

/-- Remove ZERO normals and normalize each remaining Euclidean
normal without reordering the Cartan reflection factors. -/
noncomputable def sourceEuclideanUnitNormals : List Euc48 → List Euc48
  | [] => []
  | u :: tail =>
    if _h : u = 0 then sourceEuclideanUnitNormals tail
    else FCP.BFSSS1V52K1D18V7H.euclideanUnitNormal u ::
      sourceEuclideanUnitNormals tail

/-- Every retained normal is genuinely norm one. -/
theorem sourceEuclideanUnitNormals_all_unit (l : List Euc48) :
    ∀ u ∈ sourceEuclideanUnitNormals l, ‖u‖ = 1 := by
  induction l with
  | nil =>
      simp [sourceEuclideanUnitNormals]
  | cons u tail ih =>
      intro v hv
      by_cases hu : u = 0
      · have hv' : v ∈ sourceEuclideanUnitNormals tail := by
          simpa [sourceEuclideanUnitNormals, hu] using hv
        exact ih v hv'
      · have hv' :
            v = FCP.BFSSS1V52K1D18V7H.euclideanUnitNormal u ∨
              v ∈ sourceEuclideanUnitNormals tail := by
          simpa [sourceEuclideanUnitNormals, hu] using hv
        rcases hv' with h | h
        · subst v
          exact FCP.BFSSS1V52K1D18V7H.euclideanUnitNormal_norm_one u hu
        · exact ih v h

/-- Discarding zero factors never increases Cartan list length. -/
theorem sourceEuclideanUnitNormals_length_le (l : List Euc48) :
    (sourceEuclideanUnitNormals l).length ≤ l.length := by
  induction l with
  | nil =>
      simp [sourceEuclideanUnitNormals]
  | cons u tail ih =>
      by_cases hu : u = 0
      · simp only [sourceEuclideanUnitNormals, dite_eq_left hu, List.length_cons]
        exact ih.trans (Nat.le_succ _)
      · simp only [sourceEuclideanUnitNormals, dite_eq_right hu, List.length_cons]
        exact Nat.succ_le_succ ih

/-- The ENTIRE ordered native hyperplane-reflection product is
unchanged when zero normals are omitted and the remaining normals
are normalized. This uses only accepted V7H pointwise identities. -/
theorem sourceEuclideanUnitNormals_reflectionProduct_eq (l : List Euc48) :
    (l.map fun u => (ℝ ∙ u)ᗮ.reflection).prod =
      ((sourceEuclideanUnitNormals l).map fun u => (ℝ ∙ u)ᗮ.reflection).prod := by
  induction l with
  | nil => rfl
  | cons u tail ih =>
      by_cases hu : u = 0
      · subst u
        simp only [List.map_cons, List.prod_cons,
          sourceEuclideanUnitNormals]
        rw [FCP.BFSSS1V52K1D18V7H.euclideanHyperplaneReflection_zero, one_mul]
        exact ih
      · simp only [List.map_cons, List.prod_cons,
          sourceEuclideanUnitNormals, dite_eq_right hu]
        rw [FCP.BFSSS1V52K1D18V7H.euclideanUnitNormal_reflection_eq u hu, ih]

/-- Original source SAME-LABEL Euclidean transport of a Cartan
factorization: every factor is now a genuine unit hyperplane
reflection, with zero identity factors removed, while the exact
orthogonal transformation and the dimensional length bound persist.
This is an auxiliary target-space factorization, NOT sourceSO
unit-pair generation or determinant-parity theorem. -/
theorem originalSourceEuclidean_Cartan_zeroFreeUnitNormals
    (φ : Euc48 ≃ₗᵢ[ℝ] Euc48) :
    ∃ unitNormals : List Euc48,
      (∀ u ∈ unitNormals, ‖u‖ = 1) ∧
      unitNormals.length ≤ Module.finrank ℝ Euc48 ∧
      φ = (unitNormals.map fun u => (ℝ ∙ u)ᗮ.reflection).prod := by
  rcases FCP.BFSSS1V52K1D18V7B.source48Euclidean_reflections_generate_dim φ
    with ⟨normals, hlength, hfactors⟩
  refine ⟨sourceEuclideanUnitNormals normals,
    sourceEuclideanUnitNormals_all_unit normals,
    (sourceEuclideanUnitNormals_length_le normals).trans hlength, ?_⟩
  exact hfactors.trans (sourceEuclideanUnitNormals_reflectionProduct_eq normals)

#print axioms sourceEuclideanUnitNormals
#print axioms sourceEuclideanUnitNormals_all_unit
#print axioms sourceEuclideanUnitNormals_length_le
#print axioms sourceEuclideanUnitNormals_reflectionProduct_eq
#print axioms originalSourceEuclidean_Cartan_zeroFreeUnitNormals

end
end FCP.BFSSS1V52K1D18V7I
