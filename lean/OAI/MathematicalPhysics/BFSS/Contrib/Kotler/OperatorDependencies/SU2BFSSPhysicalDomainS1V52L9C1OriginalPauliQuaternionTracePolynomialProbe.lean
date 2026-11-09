import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9B4OriginalSameBlockQuaternionConjugationProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2ColorCrossProbe

/-!
S1V52L9C1 — source-faithful native Pauli quaternion finite trace audit.

This computes the EXACT original FCP.BFSSSU2.pauli (sigma_x,sigma_y,sigma_z)
2x2 trace under the B1 +i original native SU(2) quaternion matrix,
without introducing a replacement Pauli basis, alternative SU(2),
invented color action, physical Hilbert identification or mass gap.

The polynomial R has rows B=output, columns A=input. This is only
the unscaled Pauli trace; qualification of the ORIGINAL BFSS
pairedAlgebraData.color=normalizedPauli, normalization pauliScale²=1/2,
and source adjointColorMatrix still require subsequent source transport.

STAGED UNQUALIFIED until strict pinned proof and #print axioms CI.
-/
set_option autoImplicit false
set_option maxHeartbeats 440000

namespace FCP.BFSSS1V52L9C1
noncomputable section

open Matrix
open FCP.BFSSS1V52B1
open FCP.BFSSSU2

/-- Actual source quaternion-to-color real adjoint coefficients,
in output-row/input-column order. No surrogate group defined. -/
def originalQuaternionAdjointPolynomial
    (p : SourceQuaternionCoords) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![
    p.a^2-p.b^2-p.c^2+p.d^2,   2*p.a*p.b+2*p.c*p.d,      -2*p.a*p.c+2*p.b*p.d;
    -2*p.a*p.b+2*p.c*p.d,      p.a^2-p.b^2+p.c^2-p.d^2, 2*p.a*p.d+2*p.b*p.c;
    2*p.a*p.c+2*p.b*p.d,       -2*p.a*p.d+2*p.b*p.c,    p.a^2+p.b^2-p.c^2-p.d^2
  ]

/-- The genuine original source positive-i quaternion conjugates each
literal Pauli matrix into the *same source* Pauli basis, with B output
and A input. Proved by 12 finite 2×2 matrix-entry calculations rather
than the previously failed nested four-matrix trace simplification. -/
theorem originalPauliQuaternion_matrix_conjugation
    (p : SourceQuaternionCoords) (A : Fin 3) :
    sourceQuaternionColorMatrix p * pauli A *
      (sourceQuaternionColorMatrix p).conjTranspose =
      ∑ B : Fin 3,
        (originalQuaternionAdjointPolynomial p B A : ℂ) • pauli B := by
  ext i j
  fin_cases A <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauli, sourceQuaternionColorMatrix,
      originalQuaternionAdjointPolynomial,
      Matrix.mul_apply, Matrix.smul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Fin.sum_univ_three,
      Complex.star_def, Complex.I_sq, Complex.I_mul_I] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring

/-- The exact unnormalized original Pauli trace follows from the
source matrix-conjugation theorem and the previously accepted,
source-normalization-free Pauli trace orthogonality theorem. -/
theorem originalPauliQuaternion_trace_polynomial
    (p : SourceQuaternionCoords) (B A : Fin 3) :
    Matrix.trace
      (pauli B *
        (sourceQuaternionColorMatrix p * pauli A *
          (sourceQuaternionColorMatrix p).conjTranspose)) =
      ((2 : ℝ) * originalQuaternionAdjointPolynomial p B A : ℂ) := by
  calc
    Matrix.trace
      (pauli B * (sourceQuaternionColorMatrix p * pauli A *
        (sourceQuaternionColorMatrix p).conjTranspose)) =
      ∑ C : Fin 3,
        (originalQuaternionAdjointPolynomial p C A : ℂ) *
          Matrix.trace (pauli B * pauli C) := by
            rw [originalPauliQuaternion_matrix_conjugation,
              Matrix.mul_sum, Matrix.trace_sum]
            simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    _ = ((2 : ℝ) * originalQuaternionAdjointPolynomial p B A : ℂ) := by
      simp only [pauli_trace_pair]
      simp [mul_ite, eq_comm]
      ring

#print axioms originalPauliQuaternion_matrix_conjugation
#print axioms originalPauliQuaternion_trace_polynomial

end
end FCP.BFSSS1V52L9C1
