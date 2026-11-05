import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L7C2NativeOriginalSU2ZeroSafeEulerPolarProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52C2CNativeSU2RealQuaternionMatrixBridgeProbe
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
S1V52-L7C3 — STAGED AND NOT QUALIFIED.
A structurally different, *source-faithful* route to L7B3's
universal ZYZ witness: build actual ORIGINAL native
OAI.BFSSQuantum.GaugeGroup 2 elements from norm-one real
quaternions by checking source-sized special unitarity.

These are not surrogate SU2 elements: the constructed values
inhabit the upstream original GaugeGroup 2 (= specialUnitaryGroup).
The matrix is the EXACT previously qualified positive-i source
B1 quaternionColorMatrix; no change of sign or phase, no historic
G6X/H5E8 import, no unproved construction assumption.

If its strict kernel gate passes, this provides the inverse of
native quaternion extraction on the original real unit 3-sphere,
enabling genuine Z/Y circle factor construction without replaying
the historical physical Gauss/Fock dependency graph.

Only a research proof candidate until compiler + axioms PASS.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSS1V52L7C3
noncomputable section

open Matrix
open OAI.BFSSQuantum
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52B3
open FCP.BFSSS1V52C1
open FCP.BFSSS1V52C2C

/-- An unnormalized complex quaternion matrix has the exact
adjugate/conjugate-transpose relation, independent of its norm.
This identity uses the true original 2x2 color matrix type. -/
theorem originalQuaternionComplexMatrix_adjugate
    (u v : ℂ) :
    Matrix.adjugate
      (!![u,v; -star v, star u] : ColorMatrix 2) =
    (!![u,v; -star v, star u] : ColorMatrix 2)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.conjTranspose_apply]

/-- The already-qualified positive-i real quaternion color
polynomial is EXACTLY the standard complex SU2-shaped matrix. -/
theorem originalSourceQuaternionColorMatrix_complex
    (p : SourceQuaternionCoords) :
    sourceQuaternionColorMatrix p =
      (!![
        (p.a : ℂ) + (p.b : ℂ)*Complex.I,
        (p.c : ℂ) + (p.d : ℂ)*Complex.I;
        -star ((p.c : ℂ) + (p.d : ℂ)*Complex.I),
        star ((p.a : ℂ) + (p.b : ℂ)*Complex.I)
      ] : ColorMatrix 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceQuaternionColorMatrix, sourceComplex_star_re_im] <;>
    ring

/-- The exact original real quaternion norm is the 2x2 matrix
determinant. No specialized or reconstructed gauge group. -/
theorem originalSourceQuaternionColorMatrix_det
    (p : SourceQuaternionCoords) :
    Matrix.det (sourceQuaternionColorMatrix p) =
      ((sourceQuaternionNormSq p : ℝ) : ℂ) := by
  rw [originalSourceQuaternionColorMatrix_complex]
  simp [Matrix.det_fin_two, sourceQuaternionNormSq]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Genuine Mathlib source special unitary membership follows
from exact determinant-one norm and adjugate, NOT an axiom. -/
theorem originalSourceQuaternionColorMatrix_mem_SU2
    (p : SourceQuaternionCoords)
    (hp : sourceQuaternionNormSq p = 1) :
    sourceQuaternionColorMatrix p ∈
      Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  let u : ℂ := (p.a : ℂ) + (p.b : ℂ) * Complex.I
  let v : ℂ := (p.c : ℂ) + (p.d : ℂ) * Complex.I
  let A : ColorMatrix 2 := sourceQuaternionColorMatrix p
  have hA : A = !![u,v; -star v, star u] := by
    exact originalSourceQuaternionColorMatrix_complex p
  have hAdj : Matrix.adjugate A = Aᴴ := by
    rw [hA]
    exact originalQuaternionComplexMatrix_adjugate u v
  have hDet : A.det = 1 := by
    change (sourceQuaternionColorMatrix p).det = 1
    rw [originalSourceQuaternionColorMatrix_det, hp]
    norm_num
  have hmul : A * Matrix.adjugate A = 1 := by
    simpa only [hDet, one_smul] using Matrix.mul_adjugate A
  have hUnit : A ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    rw [Matrix.star_eq_conjTranspose, ← hAdj]
    exact hmul
  exact Matrix.mem_specialUnitaryGroup_iff.mpr ⟨hUnit,hDet⟩

/-- Construct an ACTUAL upstream GaugeGroup 2 element, not an
alternate model, for any source-unit quaternion polynomial. -/
noncomputable def originalNativeOfUnitQuaternion
    (p : SourceQuaternionCoords)
    (hp : sourceQuaternionNormSq p = 1) : GaugeGroup 2 :=
  ⟨sourceQuaternionColorMatrix p,
    originalSourceQuaternionColorMatrix_mem_SU2 p hp⟩

/-- Actual original native quaternion extraction is a left
inverse of the norm-one quaternion-to-native group construction. -/
theorem originalNativeOfUnitQuaternion_coords
    (p : SourceQuaternionCoords)
    (hp : sourceQuaternionNormSq p = 1) :
    originalNativeQuaternionCoords
      (originalNativeOfUnitQuaternion p hp) = p := by
  cases p with
  | mk a b c d =>
    simp [originalNativeQuaternionCoords,
      originalNativeOfUnitQuaternion,
      sourceQuaternionColorMatrix]

#print axioms originalQuaternionComplexMatrix_adjugate
#print axioms originalSourceQuaternionColorMatrix_complex
#print axioms originalSourceQuaternionColorMatrix_det
#print axioms originalSourceQuaternionColorMatrix_mem_SU2
#print axioms originalNativeOfUnitQuaternion
#print axioms originalNativeOfUnitQuaternion_coords
end
end FCP.BFSSS1V52L7C3
