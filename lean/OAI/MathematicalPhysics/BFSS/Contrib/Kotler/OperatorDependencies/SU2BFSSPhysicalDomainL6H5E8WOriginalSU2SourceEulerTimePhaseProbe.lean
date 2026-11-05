import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8VOriginalSU2ZeroSafeEulerRadiusPolarProbe
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
L6H5E8W: EXACT original-source Pauli-time witnesses and Euler
complex phase-product transport for arbitrary g : GaugeGroup 2.

Qualified H5E8V #351 supplies original quaternion row u,v,
their middle arcsine amplitude and both zero-safe complex phases.
Qualified H5E8U #350 supplies literal original source ZYZ matrix.

We choose times by MULTIPLICATION with the ORIGINAL positive
Pauli scale, avoiding division or a new gauge representation:
  left  = (arg u + arg v) * pauliScale
  right = (arg u - arg v) * pauliScale
  mid   = (arcsin ‖v‖) * sqrt(2).
Because pauliScale^2=1/2 and pauliScale*sqrt(2)=1, these have
the exact source normalized angle sum/difference.

NO Euler factorization, group-generation assertion, or unproved
nonzero phases; polar reconstruction works even for u=0/v=0.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8W
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2PhysicalDomainL6H5E8R
open FCP.BFSSSU2PhysicalDomainL6H5E8T
open FCP.BFSSSU2PhysicalDomainL6H5E8V

/-- Left original positive-i Pauli-z real time. -/
def originalEulerLeftTime (g : GaugeGroup 2) : ℝ :=
  (Complex.arg (originalSU2RowU g) + Complex.arg (originalSU2RowV g)) *
    FCP.BFSSSU2.pauliScale

/-- Middle original positive-i Pauli-y real time. -/
def originalEulerMiddleTime (g : GaugeGroup 2) : ℝ :=
  originalSU2MiddleAngle g * Real.sqrt 2

/-- Right original positive-i Pauli-z real time. -/
def originalEulerRightTime (g : GaugeGroup 2) : ℝ :=
  (Complex.arg (originalSU2RowU g) - Complex.arg (originalSU2RowV g)) *
    FCP.BFSSSU2.pauliScale

/-- Sum of literal source z-phases equals the first quaternion phase. -/
theorem originalEuler_sourceZ_sum (g : GaugeGroup 2) :
    sourceYAngle (originalEulerLeftTime g) +
      sourceYAngle (originalEulerRightTime g) =
        Complex.arg (originalSU2RowU g) := by
  dsimp [sourceYAngle, originalEulerLeftTime, originalEulerRightTime]
  calc
    _ = Complex.arg (originalSU2RowU g) *
          (2 * FCP.BFSSSU2.pauliScale ^ 2) := by ring
    _ = Complex.arg (originalSU2RowU g) := by
          rw [FCP.BFSSSU2.pauliScale_sq]
          ring

/-- Difference of literal source z-phases equals the second quaternion phase. -/
theorem originalEuler_sourceZ_diff (g : GaugeGroup 2) :
    sourceYAngle (originalEulerLeftTime g) -
      sourceYAngle (originalEulerRightTime g) =
        Complex.arg (originalSU2RowV g) := by
  dsimp [sourceYAngle, originalEulerLeftTime, originalEulerRightTime]
  calc
    _ = Complex.arg (originalSU2RowV g) *
          (2 * FCP.BFSSSU2.pauliScale ^ 2) := by ring
    _ = Complex.arg (originalSU2RowV g) := by
          rw [FCP.BFSSSU2.pauliScale_sq]
          ring

/-- The literal Pauli-y source real time yields the arcsine angle. -/
theorem originalEuler_sourceY_middle (g : GaugeGroup 2) :
    sourceYAngle (originalEulerMiddleTime g) =
      originalSU2MiddleAngle g := by
  dsimp [sourceYAngle, originalEulerMiddleTime]
  calc
    _ = originalSU2MiddleAngle g *
          (FCP.BFSSSU2.pauliScale * Real.sqrt 2) := by ring
    _ = originalSU2MiddleAngle g := by
          rw [FCP.BFSSSU2.pauliScale_mul_sqrt, mul_one]

/-- Complex sum of the two exact original z-diagonal +i phases. -/
theorem originalEuler_sourceZ_complex_u (g : GaugeGroup 2) :
    sourceZDiagonal (originalEulerLeftTime g) 0 +
      sourceZDiagonal (originalEulerRightTime g) 0 =
        ((Complex.arg (originalSU2RowU g) : ℝ) : ℂ) * Complex.I := by
  rw [sourceZDiagonal_zero_imag, sourceZDiagonal_zero_imag,
      ← add_mul, ← Complex.ofReal_add, originalEuler_sourceZ_sum]

/-- Complex difference of the exact original z-diagonal +i phases. -/
theorem originalEuler_sourceZ_complex_v (g : GaugeGroup 2) :
    sourceZDiagonal (originalEulerLeftTime g) 0 +
      sourceZDiagonal (originalEulerRightTime g) 1 =
        ((Complex.arg (originalSU2RowV g) : ℝ) : ℂ) * Complex.I := by
  calc
    sourceZDiagonal (originalEulerLeftTime g) 0 +
        sourceZDiagonal (originalEulerRightTime g) 1 =
        ((sourceYAngle (originalEulerLeftTime g) -
            sourceYAngle (originalEulerRightTime g) : ℝ) : ℂ) *
          Complex.I := by
            rw [sourceZDiagonal_zero_imag, sourceZDiagonal_one_imag]
            push_cast
            ring
    _ = ((Complex.arg (originalSU2RowV g) : ℝ) : ℂ) *
          Complex.I := by
            rw [originalEuler_sourceZ_diff]

/-- Product of original source z-exponentials recovers u's
zero-safe complex polar phase, with no nonzero assumption. -/
theorem originalEuler_source_exp_phase_u (g : GaugeGroup 2) :
    Complex.exp (sourceZDiagonal (originalEulerLeftTime g) 0) *
      Complex.exp (sourceZDiagonal (originalEulerRightTime g) 0) =
        Complex.exp (Complex.arg (originalSU2RowU g) * Complex.I) := by
  rw [← Complex.exp_add, originalEuler_sourceZ_complex_u]

/-- Product of source z-exponentials recovers v's
zero-safe complex polar phase, with no nonzero assumption. -/
theorem originalEuler_source_exp_phase_v (g : GaugeGroup 2) :
    Complex.exp (sourceZDiagonal (originalEulerLeftTime g) 0) *
      Complex.exp (sourceZDiagonal (originalEulerRightTime g) 1) =
        Complex.exp (Complex.arg (originalSU2RowV g) * Complex.I) := by
  rw [← Complex.exp_add, originalEuler_sourceZ_complex_v]

#print axioms originalEulerLeftTime
#print axioms originalEulerMiddleTime
#print axioms originalEulerRightTime
#print axioms originalEuler_sourceZ_sum
#print axioms originalEuler_sourceZ_diff
#print axioms originalEuler_sourceY_middle
#print axioms originalEuler_sourceZ_complex_u
#print axioms originalEuler_sourceZ_complex_v
#print axioms originalEuler_source_exp_phase_u
#print axioms originalEuler_source_exp_phase_v
#check @originalEuler_source_exp_phase_v

end
end FCP.BFSSSU2PhysicalDomainL6H5E8W
