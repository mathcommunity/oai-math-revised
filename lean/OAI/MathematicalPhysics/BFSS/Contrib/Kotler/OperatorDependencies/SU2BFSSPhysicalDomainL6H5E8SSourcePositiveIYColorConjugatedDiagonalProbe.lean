import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8RSourceNormalizedZColorFlowDiagonalProbe
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
L6H5E8S: the literal original +i Pauli-y source gauge curve,
expressed by a fixed 2x2 change of basis and the now-qualified
L6H5E8R scalar exponential diagonal.

All basis-change matrices are FINITE-DIMENSIONAL PROOF WITNESSES.
We retain the original pairedAlgebraData.color, ColorIndex 2,
GaugeGroup 2, and all positive-i signs. No alternate Fock or
gauge representation and no asserted SU2 generation.

The tangent algebra, inverse witness, and finite-time matrix
exponential conjugation are separately axiom audited.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8S
noncomputable section

open Matrix
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2Full
open FCP.BFSSSU2PhysicalDomainL6G6V
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6H5E8R

/-- Fixed eigenvector columns of the source positive-i Pauli-y
skew matrix [[0,1],[-1,0]]. Algebraic proof witness only. -/
def sourceYChange : ColorMatrix 2 :=
  !![(1 : ℂ), 1; Complex.I, -Complex.I]

/-- Explicit two-sided inverse of sourceYChange. -/
def sourceYChangeInv : ColorMatrix 2 :=
  !![(1/2 : ℂ), -(Complex.I)/2; (1/2 : ℂ), Complex.I/2]

theorem sourceYChange_mul_inverse :
    sourceYChange * sourceYChangeInv = (1 : ColorMatrix 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceYChange, sourceYChangeInv, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring_nf

theorem sourceYChange_inverse_mul :
    sourceYChangeInv * sourceYChange = (1 : ColorMatrix 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceYChange, sourceYChangeInv, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring_nf <;> norm_num [Complex.I_sq]

/-- The exact source original +i y-tangent, not a substitute
matrix generator, is the fixed-conjugate of the same diagonal used
by the qualified original z-curve. -/
theorem source_y_tangent_diagonal_conjugation (t : ℝ) :
    t • ((Complex.I : ℂ) • pairedAlgebraData.color (1 : Fin 3)) =
      sourceYChange * Matrix.diagonal (sourceZDiagonal t) *
        sourceYChangeInv := by
  rw [pairedAlgebraData_color, concreteAlgebraData_color]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceYChange, sourceYChangeInv, sourceZDiagonal,
      FCP.BFSSSU2.normalizedPauli, FCP.BFSSSU2.pauli,
      Matrix.mul_apply, Matrix.vecMul_diagonal,
      Fin.sum_univ_two, Matrix.smul_apply] <;>
    ring_nf

/-- Exact source group curve as finite conjugation of pinned
scalar exponentials. The fixed 2x2 inverse witness defines a
`Units` element, permitting the pinned matrix-specialized
`Matrix.exp_units_conj` theorem. This avoids the known
noncanonical matrix multiplication instance mismatch of
`SemiconjBy.exp_right` from red #346. -/
theorem source_y_gaugeCurve_diagonal_exp_conjugation (t : ℝ) :
    (sourcePlusIGaugeCurve (1 : Fin 3) t : ColorMatrix 2) =
      sourceYChange *
        Matrix.diagonal (fun i => Complex.exp (sourceZDiagonal t i)) *
        sourceYChangeInv := by
  let A : ColorMatrix 2 :=
    t • ((Complex.I : ℂ) • pairedAlgebraData.color (1 : Fin 3))
  let D : ColorMatrix 2 := Matrix.diagonal (sourceZDiagonal t)
  have hAD : A = sourceYChange * D * sourceYChangeInv :=
    source_y_tangent_diagonal_conjugation t
  let U : (ColorMatrix 2)ˣ :=
    ⟨sourceYChange, sourceYChangeInv,
      sourceYChange_mul_inverse, sourceYChange_inverse_mul⟩
  have hU : (U : ColorMatrix 2) = sourceYChange := rfl
  have hUinv : ((U⁻¹ : (ColorMatrix 2)ˣ) : ColorMatrix 2) = sourceYChangeInv := rfl
  calc
    (sourcePlusIGaugeCurve (1 : Fin 3) t : ColorMatrix 2) =
        NormedSpace.exp A := rfl
    _ = NormedSpace.exp ((U : ColorMatrix 2) * D * ((U⁻¹ : (ColorMatrix 2)ˣ) : ColorMatrix 2)) := by
      rw [hU, hUinv, ← hAD]
    _ = (U : ColorMatrix 2) * NormedSpace.exp D * ((U⁻¹ : (ColorMatrix 2)ˣ) : ColorMatrix 2) :=
      Matrix.exp_units_conj U D
    _ = sourceYChange *
          Matrix.diagonal (fun i => Complex.exp (sourceZDiagonal t i)) *
            sourceYChangeInv := by
          rw [hU, hUinv]
          dsimp [D]
          rw [Matrix.exp_diagonal, Pi.exp_def]
          simp only [Complex.exp_eq_exp_ℂ]

#print axioms sourceYChange
#print axioms sourceYChangeInv
#print axioms sourceYChange_mul_inverse
#print axioms sourceYChange_inverse_mul
#print axioms source_y_tangent_diagonal_conjugation
#print axioms source_y_gaugeCurve_diagonal_exp_conjugation
#check @source_y_gaugeCurve_diagonal_exp_conjugation

end
end FCP.BFSSSU2PhysicalDomainL6H5E8S
