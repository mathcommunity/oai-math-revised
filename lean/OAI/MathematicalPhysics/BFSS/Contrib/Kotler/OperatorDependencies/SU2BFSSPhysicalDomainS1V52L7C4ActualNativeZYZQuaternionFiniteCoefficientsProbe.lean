import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L7C3UnitQuaternionToOriginalNativeSU2Probe
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
S1V52-L7C4 — STAGED, NOT YET QUALIFIED.

Exact positive-i original B1 quaternion Z/Y/Z circle coordinates,
norms, and finite product phases. These provide a small
original-size analytic interface for deriving L7B3's missing
universal native Euler witness from the accepted L7C2 zero-safe
polar reconstruction, without importing the unrelated historical
physical Hilbert/Gauss source chain.

All matrices, quaternion multiplication signs, and native group
references come from accepted source B1/C1/C2D and the genuine
S1V52L7C3 quaternion-to-original-native-SU2 construction.
Theorems below are NOT qualified until independent strict CI.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000
namespace FCP.BFSSS1V52L7C4
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52B3
open FCP.BFSSS1V52L7C3

/-- Original positive-i SU2 quaternion Z circle. -/
def originalNativeZQuaternion (a : ℝ) : SourceQuaternionCoords :=
  ⟨Real.cos a, Real.sin a, 0, 0⟩

/-- Original positive-i SU2 quaternion Y circle. -/
def originalNativeYQuaternion (a : ℝ) : SourceQuaternionCoords :=
  ⟨Real.cos a, 0, Real.sin a, 0⟩

/-- Exact norm-one Z circle in the original real quaternion
coordinate norm used by actual source GaugeGroup 2. -/
theorem originalNativeZQuaternion_norm (a : ℝ) :
    sourceQuaternionNormSq (originalNativeZQuaternion a) = 1 := by
  simp [sourceQuaternionNormSq, originalNativeZQuaternion]

/-- Exact norm-one positive upper-right Y circle. -/
theorem originalNativeYQuaternion_norm (a : ℝ) :
    sourceQuaternionNormSq (originalNativeYQuaternion a) = 1 := by
  simp [sourceQuaternionNormSq, originalNativeYQuaternion]

/-- Real original +i quaternion coefficients of Z(a)Y(b)Z(c),
including the crucial a+c versus a-c phase distinction.
This is the original B1 source multiplication polynomial,
not a surrogate Euler group. -/
theorem originalNativeZYZQuaternion_compose (a b c : ℝ) :
    sourceQuaternionCompose
      (sourceQuaternionCompose
        (originalNativeZQuaternion a) (originalNativeYQuaternion b))
      (originalNativeZQuaternion c) =
      (⟨Real.cos b * Real.cos (a+c),
        Real.cos b * Real.sin (a+c),
        Real.sin b * Real.cos (a-c),
        Real.sin b * Real.sin (a-c)⟩ : SourceQuaternionCoords) := by
  dsimp [sourceQuaternionCompose, originalNativeZQuaternion,
    originalNativeYQuaternion]
  congr 1 <;>
    simp [Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub] <;>
    ring

/-- The finite original +i source ZYZ matrix (0,0) complex
entry, expressed as a cosine amplitude and exact sum phase. -/
theorem originalNativeZYZQuaternion_first_u (a b c : ℝ) :
    (sourceQuaternionColorMatrix
      (sourceQuaternionCompose
        (sourceQuaternionCompose
          (originalNativeZQuaternion a) (originalNativeYQuaternion b))
        (originalNativeZQuaternion c))) 0 0 =
      (Real.cos b : ℂ) *
        ((Real.cos (a+c) : ℂ) +
          (Real.sin (a+c) : ℂ)*Complex.I) := by
  rw [originalNativeZYZQuaternion_compose]
  simp [sourceQuaternionColorMatrix]
  ring

/-- Exact source Y-sine amplitude with the DIFFERENCE of
Z angles for the (0,1) original positive-i quaternion entry. -/
theorem originalNativeZYZQuaternion_first_v (a b c : ℝ) :
    (sourceQuaternionColorMatrix
      (sourceQuaternionCompose
        (sourceQuaternionCompose
          (originalNativeZQuaternion a) (originalNativeYQuaternion b))
        (originalNativeZQuaternion c))) 0 1 =
      (Real.sin b : ℂ) *
        ((Real.cos (a-c) : ℂ) +
          (Real.sin (a-c) : ℂ)*Complex.I) := by
  rw [originalNativeZYZQuaternion_compose]
  simp [sourceQuaternionColorMatrix]
  ring

#print axioms originalNativeZQuaternion_norm
#print axioms originalNativeYQuaternion_norm
#print axioms originalNativeZYZQuaternion_compose
#print axioms originalNativeZYZQuaternion_first_u
#print axioms originalNativeZYZQuaternion_first_v
end
end FCP.BFSSS1V52L7C4
