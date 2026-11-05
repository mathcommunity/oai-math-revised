import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7FOriginalSourcePolarEuclideanLineAxisFormulaProbe
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
K1D18V7G — original-source Clifford line-axis and native Mathlib
Euclidean line/hyperplane reflection correspondence.

Carry only accepted V7F source-polar / same-label Euclidean
rank-one formula forward. Compare it with PINNED Mathlib
Submodule.reflection_singleton_apply at a source Q-unit vector.
Then use Submodule.reflection_orthogonal_apply to identify its
negative with the native hyperplane reflection. Two negatives
cancel for an original source unit pair; the resulting genuine
Spin48 pair action is the two corresponding native hyperplane
reflections, in precise source order.

ZERO general Cartan factorization / determinant parity / nonunit
normal normalization is asserted here. Source Q, source group,
actual source matrix and original Fin24 × Fin2 basis are unchanged.
No full SO generation, Spin surjectivity, covering, global Spin9,
or physical BFSS spectrum. Candidate until source-pinned strict CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V7G
noncomputable section
open FCP.BFSSS1V0
open Submodule
open Matrix

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev Euc48 := EuclideanSpace ℝ Source48Label
private abbrev E : Source48Vector ≃ₗ[ℝ] Euc48 :=
  FCP.BFSSS1V52K1D18V7C.originalSource48ToEuclidean

/-- Typed pinned-Mathlib reflection formula at an abstract unit
vector in the actual target EuclideanSpace; neither source Q
nor original source labels are unfolded by this step. -/
theorem euclideanUnitLineReflection_apply
    (u w : Euc48) (hu : ‖u‖ = 1) :
    (ℝ ∙ u).reflection w = (2 * inner ℝ u w) • u - w := by
  simpa [hu, two_smul, two_mul, add_smul] using
    (Submodule.reflection_singleton_apply (𝕜 := ℝ) u w)

/-- The ACTUAL accepted original source Clifford rank-one matrix
agrees, through V7C's same-label linear equivalence E, with
Mathlib's native LINE reflection, not a substitute formula. -/
theorem originalSourceUnitRankOne_eq_nativeEuclideanLineReflection
    (u w : Source48Vector) (hu : Q u = 1) :
    E (FCP.BFSSS1V52K1D18V6D.originalSourceUnitRankOneMatrix u hu *ᵥ w) =
      (ℝ ∙ E u).reflection (E w) := by
  rw [FCP.BFSSS1V52K1D18V7F.originalSourceUnitRankOne_euclidean_action]
  exact (euclideanUnitLineReflection_apply (E u) (E w)
    (FCP.BFSSS1V52K1D18V7F.originalSourceUnitQ_euclidean_norm_one u hu)).symm

/-- The ACTUAL source Clifford line-axis action is NEGATIVE of
the corresponding native Euclidean HYPERPLANE reflection.
The sign matters in single-factor parity arguments. -/
theorem originalSourceUnitRankOne_eq_negativeNativeHyperplaneReflection
    (u w : Source48Vector) (hu : Q u = 1) :
    E (FCP.BFSSS1V52K1D18V6D.originalSourceUnitRankOneMatrix u hu *ᵥ w) =
      -((ℝ ∙ E u)ᗮ.reflection (E w)) := by
  rw [originalSourceUnitRankOne_eq_nativeEuclideanLineReflection u w hu]
  rw [Submodule.reflection_orthogonal_apply]
  simp

/-- Pairing TWO genuine original source unit-rank-one matrices
cancels the two minus signs, so in the exact same-label auxiliary
Euclidean coordinates their action is precisely the ordered
composition of the TWO native hyperplane reflections. -/
theorem originalSourceUnitPairMatrices_eq_nativeHyperplanePairAction
    (u v w : Source48Vector) (hu : Q u = 1) (hv : Q v = 1) :
    E (FCP.BFSSS1V52K1D18V6D.originalSourceUnitRankOneMatrix u hu *ᵥ
        (FCP.BFSSS1V52K1D18V6D.originalSourceUnitRankOneMatrix v hv *ᵥ w)) =
      (ℝ ∙ E u)ᗮ.reflection ((ℝ ∙ E v)ᗮ.reflection (E w)) := by
  calc
    E (FCP.BFSSS1V52K1D18V6D.originalSourceUnitRankOneMatrix u hu *ᵥ
        (FCP.BFSSS1V52K1D18V6D.originalSourceUnitRankOneMatrix v hv *ᵥ w)) =
        -((ℝ ∙ E u)ᗮ.reflection
          (E (FCP.BFSSS1V52K1D18V6D.originalSourceUnitRankOneMatrix v hv *ᵥ w))) :=
      originalSourceUnitRankOne_eq_negativeNativeHyperplaneReflection
        u _ hu
    _ = -((ℝ ∙ E u)ᗮ.reflection
        (-((ℝ ∙ E v)ᗮ.reflection (E w)))) := by
          rw [originalSourceUnitRankOne_eq_negativeNativeHyperplaneReflection v w hv]
    _ = (ℝ ∙ E u)ᗮ.reflection ((ℝ ∙ E v)ᗮ.reflection (E w)) := by
      simp

/-- The ACTUAL original Spin48 element obtained from an exact
Clifford unit pair acts as the corresponding two native
hyperplane reflections, with no assumption of Spin surjectivity.
This is a typed original-action witness, NOT SO generation. -/
theorem originalSourceSpinUnitPair_eq_nativeHyperplanePairAction
    (u v w : Source48Vector) (hu : Q u = 1) (hv : Q v = 1) :
    E (FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry
      (FCP.BFSSS1V52K1D18V6C.originalSourceUnitPairSpin u v hu hv) w) =
      (ℝ ∙ E u)ᗮ.reflection ((ℝ ∙ E v)ᗮ.reflection (E w)) := by
  rw [FCP.BFSSS1V52K1D18V6D.originalSourceUnitPairSpin_action_no_instance_premises]
  exact originalSourceUnitPairMatrices_eq_nativeHyperplanePairAction u v w hu hv

#print axioms euclideanUnitLineReflection_apply
#print axioms originalSourceUnitRankOne_eq_nativeEuclideanLineReflection
#print axioms originalSourceUnitRankOne_eq_negativeNativeHyperplaneReflection
#print axioms originalSourceUnitPairMatrices_eq_nativeHyperplanePairAction
#print axioms originalSourceSpinUnitPair_eq_nativeHyperplanePairAction

end
end FCP.BFSSS1V52K1D18V7G
