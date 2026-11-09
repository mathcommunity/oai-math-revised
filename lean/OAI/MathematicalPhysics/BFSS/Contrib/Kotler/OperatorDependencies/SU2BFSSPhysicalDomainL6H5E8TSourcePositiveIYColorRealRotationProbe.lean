import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8SSourcePositiveIYColorConjugatedDiagonalProbe
import Mathlib.Analysis.Complex.Trigonometric

/-!
L6H5E8T: explicit real-rotation matrix of the ORIGINAL +i Pauli-y
source color curve.

Qualified predecessors: H5E8R source z diagonal exponential (#345),
H5E8S original y diagonal conjugation (#348).
All computations stay in the original ColorMatrix 2 and
pairedAlgebraData.color, with positive-i source convention.
Only the finite matrix/scalar exponential identities are targeted.
No group generation or Fock-space inference.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8T
noncomputable section

open Matrix
open OAI.BFSSQuantum
open FCP.BFSSSU2PhysicalDomainL6H5E8R
open FCP.BFSSSU2PhysicalDomainL6H5E8S
open FCP.BFSSSU2PhysicalDomainL6G6X

/-- The original normalized-Pauli real-time angle, not an
additional free phase or a changed color convention. -/
def sourceYAngle (t : ℝ) : ℝ := t * FCP.BFSSSU2.pauliScale

theorem sourceZDiagonal_zero_imag (t : ℝ) :
    sourceZDiagonal t (0 : Fin 2) =
      ((sourceYAngle t : ℝ) : ℂ) * Complex.I := by
  simp [sourceZDiagonal, sourceYAngle]
  ring

theorem sourceZDiagonal_one_imag (t : ℝ) :
    sourceZDiagonal t (1 : Fin 2) =
      -(((sourceYAngle t : ℝ) : ℂ) * Complex.I) := by
  simp [sourceZDiagonal, sourceYAngle]
  ring

theorem sourceZDiagonal_exp_zero (t : ℝ) :
    Complex.exp (sourceZDiagonal t (0 : Fin 2)) =
      (Real.cos (sourceYAngle t) : ℂ) +
        (Real.sin (sourceYAngle t) : ℂ) * Complex.I := by
  rw [sourceZDiagonal_zero_imag, Complex.exp_ofReal_mul_I]

theorem sourceZDiagonal_exp_one (t : ℝ) :
    Complex.exp (sourceZDiagonal t (1 : Fin 2)) =
      (Real.cos (sourceYAngle t) : ℂ) -
        (Real.sin (sourceYAngle t) : ℂ) * Complex.I := by
  calc
    Complex.exp (sourceZDiagonal t (1 : Fin 2)) =
        Complex.exp (((-sourceYAngle t : ℝ) : ℂ) * Complex.I) := by
          rw [sourceZDiagonal_one_imag]
          push_cast
          ring
    _ = (Real.cos (sourceYAngle t) : ℂ) -
          (Real.sin (sourceYAngle t) : ℂ) * Complex.I := by
          rw [Complex.exp_ofReal_mul_I]
          simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
          ring

/-- Source-exact positive-i y curve, now written as the
explicit real SO(2)-form inside original ColorMatrix 2. -/
def sourceYRotation (t : ℝ) : ColorMatrix 2 :=
  !![(Real.cos (sourceYAngle t) : ℂ), (Real.sin (sourceYAngle t) : ℂ);
     -(Real.sin (sourceYAngle t) : ℂ), (Real.cos (sourceYAngle t) : ℂ)]

theorem source_y_gaugeCurve_real_rotation (t : ℝ) :
    (sourcePlusIGaugeCurve (1 : Fin 3) t : ColorMatrix 2) =
      sourceYRotation t := by
  rw [source_y_gaugeCurve_diagonal_exp_conjugation]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceYRotation, sourceYChange, sourceYChangeInv,
      sourceZDiagonal_exp_zero, sourceZDiagonal_exp_one,
      Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_two] <;>
    ring_nf <;> norm_num [Complex.I_sq]

#print axioms sourceYAngle
#print axioms sourceZDiagonal_zero_imag
#print axioms sourceZDiagonal_one_imag
#print axioms sourceZDiagonal_exp_zero
#print axioms sourceZDiagonal_exp_one
#print axioms sourceYRotation
#print axioms source_y_gaugeCurve_real_rotation
#check @source_y_gaugeCurve_real_rotation

end
end FCP.BFSSSU2PhysicalDomainL6H5E8T
