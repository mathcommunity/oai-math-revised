import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18DOriginalSourceSpinUnitFactorizationProbe
import Mathlib.LinearAlgebra.Determinant

/-!
K1D18E: exact original Spin(48) linear-map determinant equals +1
UNDER a source-exact factorization of its Clifford unit into TWO
invertible original Clifford vector generators.

This is NOT a theorem that every source spinGroup element has this
two-unit factorization: general Lipschitz closure/even parity is open.

We bridge the exact original K1D13 linear map to the composed ACTUAL
K1D18C source rank-one matrices via a typed equality with pinned
Matrix.toLin', then apply the actual LinearMap.det-to-matrix lemma.
No replacement 48-label basis, alternative form, group action,
extra axioms, or elaboration-limit changes are introduced.
Unaccepted candidate until strict independent pinned source CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18E
noncomputable section

open FCP.BFSSS1V0
open Matrix

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- Only a transparent shorthand for the actual original S1V37
rank-one matrix and its original K1D18B normalized polar row. -/
private abbrev sourceMatrix
    (a : Source48Vector) [Invertible (Q a)] :
    Matrix Source48Label Source48Label ℝ :=
  FCP.BFSSS1V37.source48_rankOneConjugationMatrix a
    (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow a)

/-- The product of TWO exact original generator conjugation matrices
has determinant +1 on the original 48-real source vector space. -/
theorem originalSourceTwoGeneratorMatrices_det_one
    (a b : Source48Vector) [Invertible (Q a)] [Invertible (Q b)] :
    (sourceMatrix a * sourceMatrix b).det = (1 : ℝ) := by
  have ha : (sourceMatrix a).det = (-1 : ℝ) :=
    FCP.BFSSS1V52K1D18C.source48_original_generator_rankOneMatrix_det a
  have hb : (sourceMatrix b).det = (-1 : ℝ) :=
    FCP.BFSSS1V52K1D18C.source48_original_generator_rankOneMatrix_det b
  rw [Matrix.det_mul, ha, hb]
  norm_num

/-- Given the stated equality of the actual source Spin unit with
a two-generator unit product, the original K1D13 Spin real-linear
action is IDENTICAL to the matrix-based map. This proves a bridge,
not factorization existence. -/
theorem originalSourceSpin48LinearMap_eq_twoGeneratorToLin_of_unitFactorization
    (s : spinGroup Q) (a b : Source48Vector)
    [Invertible (CliffordAlgebra.ι Q a)] [Invertible (Q a)]
    [Invertible (CliffordAlgebra.ι Q b)] [Invertible (Q b)]
    (hfactor : spinGroup.toUnits s =
      unitOfInvertible (CliffordAlgebra.ι Q a) *
        unitOfInvertible (CliffordAlgebra.ι Q b)) :
    FCP.BFSSS1V52K1D13.originalSourceSpin48LinearMap s =
      Matrix.toLin' (sourceMatrix a * sourceMatrix b) := by
  apply LinearMap.ext
  intro v
  change FCP.BFSSS1V31.sourceSpin48VectorAction s v =
    Matrix.toLin' (sourceMatrix a * sourceMatrix b) v
  rw [Matrix.toLin'_apply]
  calc
    FCP.BFSSS1V31.sourceSpin48VectorAction s v =
        FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry s v := rfl
    _ = sourceMatrix a *ᵥ (sourceMatrix b *ᵥ v) :=
      FCP.BFSSS1V52K1D18D.originalSourceSpin48Isometry_twoGeneratorMatrices_of_unitFactorization
        s a b v hfactor
    _ = (sourceMatrix a * sourceMatrix b) *ᵥ v := by
      rw [Matrix.mulVec_mulVec]

/-- Source-exact determinant +1 of the GENUINE K1D13 source Spin(48)
linear map under an explicit two-original-generator unit factorization.
No claim of general factorization or universal orientation is made. -/
theorem originalSourceSpin48LinearMap_det_one_of_twoUnitFactorization
    (s : spinGroup Q) (a b : Source48Vector)
    [Invertible (CliffordAlgebra.ι Q a)] [Invertible (Q a)]
    [Invertible (CliffordAlgebra.ι Q b)] [Invertible (Q b)]
    (hfactor : spinGroup.toUnits s =
      unitOfInvertible (CliffordAlgebra.ι Q a) *
        unitOfInvertible (CliffordAlgebra.ι Q b)) :
    LinearMap.det (FCP.BFSSS1V52K1D13.originalSourceSpin48LinearMap s) =
      (1 : ℝ) := by
  rw [originalSourceSpin48LinearMap_eq_twoGeneratorToLin_of_unitFactorization
    s a b hfactor, LinearMap.det_toLin']
  exact originalSourceTwoGeneratorMatrices_det_one a b

#print axioms originalSourceTwoGeneratorMatrices_det_one
#print axioms originalSourceSpin48LinearMap_eq_twoGeneratorToLin_of_unitFactorization
#print axioms originalSourceSpin48LinearMap_det_one_of_twoUnitFactorization

end
end FCP.BFSSS1V52K1D18E
