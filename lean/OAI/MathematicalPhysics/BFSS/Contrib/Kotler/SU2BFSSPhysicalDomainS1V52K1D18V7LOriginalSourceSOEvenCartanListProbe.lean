import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7KNativeCartanUnitFactorDeterminantProductProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7EOriginalSourceSOEuclideanDeterminantTransportProbe
import Mathlib.Algebra.Ring.Parity
import Mathlib.LinearAlgebra.Determinant

/-!
K1D18V7L — actual original sourceSO even native Cartan list.

Strictly accepted V7I provides an ordered Euclidean unit-normal
hyperplane-reflection list for ANY true isometry, with a length bound.
Strictly accepted V7K gives the determinant of its actual product as
(-1)^list.length. Strictly accepted V7E transports original sourceSO
determinant +1 to its ACTUAL same-label Euclidean isometry.

Pinned Mathlib provides neg_one_pow_eq_one_iff_even over real scalars.
This candidate tests the exact missing parity step without changing
original source Q, sourceSO carrier, the fixed 48 labels, Clifford
generators or the product order.

Even list factorization does NOT yet yield original Q-unit witnesses,
source Spin pair generators, full Spin48 image surjectivity, topological
covering, Spin9 lift or BFSS physical spectral existence. Both roots
are CANDIDATES pending independent strict Lean compiler/axiom audits.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V7L
noncomputable section
open FCP.BFSSS1V0
open Submodule

private abbrev Euc48 := EuclideanSpace ℝ Source48Label
private abbrev SourceSO :=
  FCP.BFSSS1V52K1D18R.source48SpecialOrthogonalWitnessGL

/-- A genuine norm-one Euclidean hyperplane-reflection list with
real determinant +1 must have even length. No original sourceSO
hypothesis is hidden here; this is a statement about its actual
native reflection product and accepted V7K determinant formula. -/
theorem euclideanUnitReflectionList_even_of_det_one
    (l : List Euc48) (hall : ∀ u ∈ l, ‖u‖ = 1)
    (hdet :
      LinearMap.det
        (((l.map fun u => (ℝ ∙ u)ᗮ.reflection).prod).toLinearMap) = 1) :
    Even l.length := by
  have hpow : (-1 : ℝ) ^ l.length = 1 := by
    calc
      (-1 : ℝ) ^ l.length =
          LinearMap.det (((l.map fun u => (ℝ ∙ u)ᗮ.reflection).prod).toLinearMap) :=
        (FCP.BFSSS1V52K1D18V7K.euclideanUnitReflectionList_det l hall).symm
      _ = 1 := hdet
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hpow

/-- EVERY element of the ACTUAL original sourceSO subgroup,
transported by accepted V7D to the original same-label Euclidean
space, has an ordered factorization by unit-normal native hyperplane
reflections of EVEN length (and bounded by the true 48 finrank).
No source Clifford Spin unit-pair action is identified here. -/
theorem originalSourceSO_has_evenUnitCartanFactorization
    (g : SourceSO) :
    ∃ unitNormals : List Euc48,
      (∀ u ∈ unitNormals, ‖u‖ = 1) ∧
      unitNormals.length ≤ Module.finrank ℝ Euc48 ∧
      Even unitNormals.length ∧
      FCP.BFSSS1V52K1D18V7D.sourceSO_toEuclideanIsometry g =
        (unitNormals.map fun u => (ℝ ∙ u)ᗮ.reflection).prod := by
  let φ : Euc48 ≃ₗᵢ[ℝ] Euc48 :=
    FCP.BFSSS1V52K1D18V7D.sourceSO_toEuclideanIsometry g
  rcases FCP.BFSSS1V52K1D18V7I.originalSourceEuclidean_Cartan_zeroFreeUnitNormals φ
    with ⟨unitNormals, hall, hlen, hfactor⟩
  have hdet : LinearMap.det φ.toLinearMap = 1 := by
    have hunit : LinearEquiv.det φ.toLinearEquiv = 1 :=
      FCP.BFSSS1V52K1D18V7E.originalSourceSO_euclideanIsometry_det_one g
    have hval : ((LinearEquiv.det φ.toLinearEquiv : ℝˣ) : ℝ) = 1 :=
      congrArg (fun z : ℝˣ => (z : ℝ)) hunit
    simpa only [LinearEquiv.coe_det] using hval
  have hfactorDet :
      LinearMap.det
        (((unitNormals.map fun u => (ℝ ∙ u)ᗮ.reflection).prod).toLinearMap) = 1 := by
    calc
      LinearMap.det
          (((unitNormals.map fun u => (ℝ ∙ u)ᗮ.reflection).prod).toLinearMap) =
          LinearMap.det φ.toLinearMap :=
        congrArg
          (fun x : Euc48 ≃ₗᵢ[ℝ] Euc48 => LinearMap.det x.toLinearMap)
          hfactor.symm
      _ = 1 := hdet
  refine ⟨unitNormals, hall, hlen, ?_, hfactor⟩
  exact euclideanUnitReflectionList_even_of_det_one unitNormals hall hfactorDet

#print axioms euclideanUnitReflectionList_even_of_det_one
#print axioms originalSourceSO_has_evenUnitCartanFactorization

end
end FCP.BFSSS1V52K1D18V7L
