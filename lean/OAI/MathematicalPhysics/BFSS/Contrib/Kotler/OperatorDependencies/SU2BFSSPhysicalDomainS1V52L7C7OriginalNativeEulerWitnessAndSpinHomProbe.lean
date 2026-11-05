import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L7C6OriginalNativeZeroSafeEulerPhaseBridgeProbe

/-!
S1V52-L7C7 — STAGED / UNQUALIFIED universal native Euler
witness and genuine original native SU2 → Spin48 hom, via
the new SMALL source-conservative C1/C2/L7C2-L7C6 path.

This route does NOT assert that the explicitly constructed
original-native Z/Y circles are the same *named historical*
sourcePlusIGaugeCurve one-parameter subgroups. It directly
constructs elements in the ACTUAL upstream GaugeGroup 2,
and thereby discharges the exact hypothesis of the previously
kernel-accepted L7B3 conditional hom. The distinction matters.

The zero-safe polar phases cover vanishing first-row entries.
Original positive-i quaternion signs, original color matrix,
genuine original source48Quadratic and Mathlib spinGroup are
all retained. No t/2 normalization, unproved assumption,
different SU2 group or physical Hilbert claim.

This source is NOT qualified until upstream L7C4-L7C6
are independently accepted, followed by its own strict CI
and complete permitted-axiom audit. No claims about global
continuity, original sixteen-block action or BFSS spectrum.
-/
set_option autoImplicit false
set_option maxHeartbeats 490000

namespace FCP.BFSSS1V52L7C7
noncomputable section

open Matrix
open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52B2
open FCP.BFSSS1V52C1
open FCP.BFSSS1V52C2B
open FCP.BFSSS1V52L7B3
open FCP.BFSSS1V52L7C2
open FCP.BFSSS1V52L7C4
open FCP.BFSSS1V52L7C5
open FCP.BFSSS1V52L7C6

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

private def zyz (g : GaugeGroup 2) : GaugeGroup 2 :=
  (originalNativeZCircle (originalNativeEulerLeftAngle g) *
      originalNativeYCircle (originalNativeMiddleAngle g)) *
    originalNativeZCircle (originalNativeEulerRightAngle g)

/-- Native ZYZ element reconstructs the original complex u entry,
including u=0, with no changed source phase convention. -/
theorem originalNativeZYZ_reconstruct_u (g : GaugeGroup 2) :
    ((zyz g : GaugeGroup 2) : ColorMatrix 2) 0 0 =
      (g : ColorMatrix 2) 0 0 := by
  change (((originalNativeZCircle (originalNativeEulerLeftAngle g) *
      originalNativeYCircle (originalNativeMiddleAngle g)) *
      originalNativeZCircle (originalNativeEulerRightAngle g) :
      GaugeGroup 2) : ColorMatrix 2) 0 0 =
    (g : ColorMatrix 2) 0 0
  rw [originalNativeZYZCircle_matrix]
  calc
    (sourceQuaternionColorMatrix
      (⟨Real.cos (originalNativeMiddleAngle g) *
            Real.cos (originalNativeEulerLeftAngle g + originalNativeEulerRightAngle g),
          Real.cos (originalNativeMiddleAngle g) *
            Real.sin (originalNativeEulerLeftAngle g + originalNativeEulerRightAngle g),
          Real.sin (originalNativeMiddleAngle g) *
            Real.cos (originalNativeEulerLeftAngle g - originalNativeEulerRightAngle g),
          Real.sin (originalNativeMiddleAngle g) *
            Real.sin (originalNativeEulerLeftAngle g - originalNativeEulerRightAngle g)⟩ :
              SourceQuaternionCoords)) 0 0 =
      (Real.cos (originalNativeMiddleAngle g) : ℂ) *
        ((Real.cos (originalNativeEulerLeftAngle g + originalNativeEulerRightAngle g) : ℂ) +
          (Real.sin (originalNativeEulerLeftAngle g + originalNativeEulerRightAngle g) : ℂ) *
             Complex.I) := by
        simp [sourceQuaternionColorMatrix, Complex.ofReal_mul]
        ring
    _ = (g : ColorMatrix 2) 0 0 :=
      originalNativeEulerPhase_reconstruct_u g

/-- Native ZYZ element reconstructs original complex v entry,
including v=0 and its positive upper-right source sign. -/
theorem originalNativeZYZ_reconstruct_v (g : GaugeGroup 2) :
    ((zyz g : GaugeGroup 2) : ColorMatrix 2) 0 1 =
      (g : ColorMatrix 2) 0 1 := by
  change (((originalNativeZCircle (originalNativeEulerLeftAngle g) *
      originalNativeYCircle (originalNativeMiddleAngle g)) *
      originalNativeZCircle (originalNativeEulerRightAngle g) :
      GaugeGroup 2) : ColorMatrix 2) 0 1 =
    (g : ColorMatrix 2) 0 1
  rw [originalNativeZYZCircle_matrix]
  calc
    (sourceQuaternionColorMatrix
      (⟨Real.cos (originalNativeMiddleAngle g) *
            Real.cos (originalNativeEulerLeftAngle g + originalNativeEulerRightAngle g),
          Real.cos (originalNativeMiddleAngle g) *
            Real.sin (originalNativeEulerLeftAngle g + originalNativeEulerRightAngle g),
          Real.sin (originalNativeMiddleAngle g) *
            Real.cos (originalNativeEulerLeftAngle g - originalNativeEulerRightAngle g),
          Real.sin (originalNativeMiddleAngle g) *
            Real.sin (originalNativeEulerLeftAngle g - originalNativeEulerRightAngle g)⟩ :
              SourceQuaternionCoords)) 0 1 =
      (Real.sin (originalNativeMiddleAngle g) : ℂ) *
        ((Real.cos (originalNativeEulerLeftAngle g - originalNativeEulerRightAngle g) : ℂ) +
          (Real.sin (originalNativeEulerLeftAngle g - originalNativeEulerRightAngle g) : ℂ) *
             Complex.I) := by
        simp [sourceQuaternionColorMatrix, Complex.ofReal_mul]
        ring
    _ = (g : ColorMatrix 2) 0 1 :=
      originalNativeEulerPhase_reconstruct_v g

/-- Exact universal factorization in ACTUAL original GaugeGroup 2,
not a surrogate SU2 and not an assumption. -/
theorem originalNativeZYZ_exact_euler (g : GaugeGroup 2) :
    zyz g = g := by
  apply Subtype.ext
  calc
    (zyz g : ColorMatrix 2) =
      !![(zyz g : ColorMatrix 2) 0 0, (zyz g : ColorMatrix 2) 0 1;
        -star ((zyz g : ColorMatrix 2) 0 1),
        star ((zyz g : ColorMatrix 2) 0 0)] :=
      originalNativeSU2_wholeQuaternionMatrix (zyz g)
    _ = !![(g : ColorMatrix 2) 0 0, (g : ColorMatrix 2) 0 1;
        -star ((g : ColorMatrix 2) 0 1), star ((g : ColorMatrix 2) 0 0)] := by
          rw [originalNativeZYZ_reconstruct_u, originalNativeZYZ_reconstruct_v]
    _ = (g : ColorMatrix 2) :=
      (originalNativeSU2_wholeQuaternionMatrix g).symm

/-- Discharge the EXACT previously qualified L7B3 Euler witness
for EVERY element of the original upstream GaugeGroup 2. -/
theorem originalNativeAll_ZYZWitness :
    ∀ g : GaugeGroup 2, originalNativeHasZYZWitness g := by
  intro g
  unfold originalNativeHasZYZWitness
  refine ⟨
    originalNativeZCircle (originalNativeEulerLeftAngle g),
    originalNativeYCircle (originalNativeMiddleAngle g),
    originalNativeZCircle (originalNativeEulerRightAngle g),
    Real.cos (originalNativeEulerLeftAngle g),
    Real.sin (originalNativeEulerLeftAngle g),
    Real.cos (originalNativeMiddleAngle g),
    Real.sin (originalNativeMiddleAngle g),
    Real.cos (originalNativeEulerRightAngle g),
    Real.sin (originalNativeEulerRightAngle g),
    ?_, ?_, ?_, ?_⟩
  · exact (originalNativeZYZ_exact_euler g).symm
  · simpa only [originalNativeZQuaternion] using
      originalNativeZCircle_coords (originalNativeEulerLeftAngle g)
  · simpa only [originalNativeYQuaternion] using
      originalNativeYCircle_coords (originalNativeMiddleAngle g)
  · simpa only [originalNativeZQuaternion] using
      originalNativeZCircle_coords (originalNativeEulerRightAngle g)

/-- Conditional L7B3 genuine native-group hom specialized with
the now source-derived UNCONDITIONAL genuine Euler witness. -/
noncomputable def originalNativeGaugeSpinHom (α : RealSpinBlock) :
    GaugeGroup 2 →* spinGroup Q :=
  originalNativeGaugeSpinHom_of_ZYZ α originalNativeAll_ZYZWitness

/-- Exact original source48 Clifford underlying map. -/
theorem originalNativeGaugeSpinHom_coe (α : RealSpinBlock) (g : GaugeGroup 2) :
    ((originalNativeGaugeSpinHom α g : spinGroup Q) : C) =
      sourceCliffordQuaternion α (originalNativeQuaternionCoords g) :=
    originalNativeGaugeSpinHom_of_ZYZ_coe
      α originalNativeAll_ZYZWitness g

#print axioms originalNativeZYZ_reconstruct_u
#print axioms originalNativeZYZ_reconstruct_v
#print axioms originalNativeZYZ_exact_euler
#print axioms originalNativeAll_ZYZWitness
#print axioms originalNativeGaugeSpinHom
#print axioms originalNativeGaugeSpinHom_coe
end
end FCP.BFSSS1V52L7C7
