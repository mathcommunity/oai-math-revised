import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L7C4ActualNativeZYZQuaternionFiniteCoefficientsProbe

/-!
S1V52-L7C5 — STAGED, NOT YET LEAN QUALIFIED.

Use the original L7C3 norm-one quaternion → ACTUAL upstream
GaugeGroup 2 construction to make genuine native positive-i
Z(a), Y(b) factors, and L7C4's exact source quaternion ZYZ
multiplication to obtain a finite native product formula.

Only original B1/C1/C2C/C2D/L7C3 matrix and group definitions.
These are not replacements for the historical sourcePlusIGaugeCurve
unless a separate all-time native equality is proved.
They are an independently verifiable genuine-native Euler factor
interface, aimed at the L7B3 universal witness.

Exact original positive-i quaternion signs and a+c vs a-c phases.
Source imports L7C4, which is not accepted until its strict CI.
No new source SU2 group, original BFSS Hamiltonian or Spin spectrum.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000

namespace FCP.BFSSS1V52L7C5
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52C1
open FCP.BFSSS1V52C2C
open FCP.BFSSS1V52C2D
open FCP.BFSSS1V52L7C3
open FCP.BFSSS1V52L7C4

/-- Genuine original native SU2 Z circle of source-positive-i phase. -/
noncomputable def originalNativeZCircle (a : ℝ) : GaugeGroup 2 :=
  originalNativeOfUnitQuaternion (originalNativeZQuaternion a)
    (originalNativeZQuaternion_norm a)

/-- Genuine original native SU2 Y circle, positive real upper-right sine. -/
noncomputable def originalNativeYCircle (a : ℝ) : GaugeGroup 2 :=
  originalNativeOfUnitQuaternion (originalNativeYQuaternion a)
    (originalNativeYQuaternion_norm a)

/-- Coordinate extraction for ACTUAL native Z circle, without hypotheses. -/
theorem originalNativeZCircle_coords (a : ℝ) :
    originalNativeQuaternionCoords (originalNativeZCircle a) =
      originalNativeZQuaternion a := by
  exact originalNativeOfUnitQuaternion_coords
    (originalNativeZQuaternion a) (originalNativeZQuaternion_norm a)

/-- Coordinate extraction for ACTUAL native Y circle. -/
theorem originalNativeYCircle_coords (a : ℝ) :
    originalNativeQuaternionCoords (originalNativeYCircle a) =
      originalNativeYQuaternion a := by
  exact originalNativeOfUnitQuaternion_coords
    (originalNativeYQuaternion a) (originalNativeYQuaternion_norm a)

/-- Original true GaugeGroup product carries exactly the
positive-i quaternion Euler coefficients. -/
theorem originalNativeZYZCircle_coords (a b c : ℝ) :
    originalNativeQuaternionCoords
      ((originalNativeZCircle a * originalNativeYCircle b) *
        originalNativeZCircle c) =
      (⟨Real.cos b * Real.cos (a+c),
        Real.cos b * Real.sin (a+c),
        Real.sin b * Real.cos (a-c),
        Real.sin b * Real.sin (a-c)⟩ : SourceQuaternionCoords) := by
  rw [originalNativeQuaternionCoords_mul,
    originalNativeQuaternionCoords_mul,
    originalNativeZCircle_coords,
    originalNativeYCircle_coords,
    originalNativeZCircle_coords]
  exact originalNativeZYZQuaternion_compose a b c

/-- The ACTUAL original native SU2 matrix of the finite ZYZ group
product is the exact B1 source quaternion matrix, at both phases. -/
theorem originalNativeZYZCircle_matrix (a b c : ℝ) :
    (((originalNativeZCircle a * originalNativeYCircle b) *
      originalNativeZCircle c : GaugeGroup 2) : ColorMatrix 2) =
      sourceQuaternionColorMatrix
        (⟨Real.cos b * Real.cos (a+c),
          Real.cos b * Real.sin (a+c),
          Real.sin b * Real.cos (a-c),
          Real.sin b * Real.sin (a-c)⟩ : SourceQuaternionCoords) := by
  calc
    ((((originalNativeZCircle a * originalNativeYCircle b) *
        originalNativeZCircle c : GaugeGroup 2) : ColorMatrix 2)) =
      sourceQuaternionColorMatrix
        (originalNativeQuaternionCoords
          ((originalNativeZCircle a * originalNativeYCircle b) *
            originalNativeZCircle c)) := by
            exact (originalNativeQuaternion_matrix_reconstruction _).symm
    _ = _ := by rw [originalNativeZYZCircle_coords]

#print axioms originalNativeZCircle
#print axioms originalNativeYCircle
#print axioms originalNativeZCircle_coords
#print axioms originalNativeYCircle_coords
#print axioms originalNativeZYZCircle_coords
#print axioms originalNativeZYZCircle_matrix
end
end FCP.BFSSS1V52L7C5
