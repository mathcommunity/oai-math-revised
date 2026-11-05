import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6WAmbientAdjointCoefficientDerivativeProbe

/-!
L6G6X — the ORIGINAL +i curve inside GaugeGroup 2.

For 2-by-2 matrices, the adjugate is a conjugated transpose. This
gives det(exp W) = 1 for traceless W using the pinned exponential
semiconjugacy and inverse laws, without a general det-exp theorem.
Apply this finite-dimensional result to the exact source color
matrices, construct the genuine SU(2) curve, and recover W as the
derivative of the native AlgebraData.adjointCoefficient.

Boundary: no derivative of the exterior/Fock representation, bounded
fermion generator identification, full Gauss constraint, or spectrum.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G6X
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2PhysicalDomainL6G6V

private def matrixTwoForm : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; -1, 0]

private theorem matrixTwoForm_mul_neg :
    matrixTwoForm * (-matrixTwoForm) = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [matrixTwoForm, Matrix.mul_apply, Fin.sum_univ_two]

private theorem matrixTwoForm_adjugate
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.adjugate X = matrixTwoForm * Xᵀ * (-matrixTwoForm) := by
  rw [Matrix.adjugate_fin_two]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [matrixTwoForm, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two]

/-- The exact 2-by-2 determinant identity, with its trace premise
visible and no Hermiticity or gauge assumption. -/
theorem twoByTwo_exp_det_one_of_trace_zero
    (W : Matrix (Fin 2) (Fin 2) ℂ) (hW : Matrix.trace W = 0) :
    Matrix.det (NormedSpace.exp W) = 1 := by
  let : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
    .restrictScalars ℚ ℂ (Matrix (Fin 2) (Fin 2) ℂ)
  have htrace : W 0 0 + W 1 1 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_two] using hW
  have h11 : W 1 1 = -(W 0 0) := by
    calc
      W 1 1 = (W 0 0 + W 1 1) - W 0 0 := by ring
      _ = -(W 0 0) := by rw [htrace]; simp
  have hsem : SemiconjBy matrixTwoForm Wᵀ (-W) := by
    change matrixTwoForm * Wᵀ = (-W) * matrixTwoForm
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [matrixTwoForm, Matrix.mul_apply, Fin.sum_univ_two, h11]
  have hexp := hsem.exp_right
  change matrixTwoForm * NormedSpace.exp Wᵀ =
    NormedSpace.exp (-W) * matrixTwoForm at hexp
  rw [Matrix.exp_transpose] at hexp
  have hadj : Matrix.adjugate (NormedSpace.exp W) =
      NormedSpace.exp (-W) := by
    rw [matrixTwoForm_adjugate, hexp, mul_assoc,
      matrixTwoForm_mul_neg, mul_one]
  have hinv : NormedSpace.exp W * NormedSpace.exp (-W) = 1 := by
    rw [← NormedSpace.exp_add_of_commute (Commute.refl W).neg_right,
      add_neg_cancel, NormedSpace.exp_zero]
  have hprod := Matrix.mul_adjugate (NormedSpace.exp W)
  rw [hadj, hinv] at hprod
  simpa using
    congrArg (fun Z : Matrix (Fin 2) (Fin 2) ℂ => Z 0 0) hprod.symm

/-- Determinant one for the exact source +i curve, obtained from the
original color-traceless field rather than an added group premise. -/
theorem sourcePlusIColorMatrix_det_one (c : ColorIndex 2) (t : ℝ) :
    Matrix.det (sourcePlusIColorMatrix c t) = 1 := by
  unfold sourcePlusIColorMatrix
  apply twoByTwo_exp_det_one_of_trace_zero
  simp only [Matrix.trace_smul, pairedAlgebraData.color_traceless c, smul_zero]

theorem sourcePlusIColorMatrix_mem_specialUnitary
    (c : ColorIndex 2) (t : ℝ) :
    sourcePlusIColorMatrix c t ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  apply Matrix.mem_specialUnitaryGroup_iff.mpr
  exact ⟨sourcePlusIColorMatrix_unitary c t,
    sourcePlusIColorMatrix_det_one c t⟩

/-- A genuine curve in the ORIGINAL determinant-one gauge group.
Its underlying matrix remains exactly the already qualified +i curve. -/
noncomputable def sourcePlusIGaugeCurve (c : ColorIndex 2) (t : ℝ) :
    GaugeGroup 2 :=
  ⟨sourcePlusIColorMatrix c t, sourcePlusIColorMatrix_mem_specialUnitary c t⟩

@[simp] theorem sourcePlusIGaugeCurve_coe (c : ColorIndex 2) (t : ℝ) :
    (sourcePlusIGaugeCurve c t : ColorMatrix 2) = sourcePlusIColorMatrix c t := rfl

theorem sourcePlusIGaugeCurve_one (c : ColorIndex 2) :
    sourcePlusIGaugeCurve c 0 = 1 := by
  apply Subtype.ext
  exact sourcePlusIColorMatrix_one c

/-- Actual native gauge-adjoint derivative: A is input, B is output.
The tangent f_(B A c) retains the source +i convention. -/
theorem sourcePlusIGaugeCurve_adjointCoefficient_deriv
    (c A B : ColorIndex 2) :
    HasDerivAt
      (fun t : ℝ => pairedAlgebraData.adjointCoefficient
        (sourcePlusIGaugeCurve c t) A B)
      (pairedAlgebraData.structureConstant B A c) 0 := by
  simpa only [AlgebraData.adjointCoefficient, sourcePlusIGaugeCurve_coe] using
    FCP.BFSSSU2PhysicalDomainL6G6W.sourcePlusIAmbientAdjointCoefficient_deriv c B A

#print axioms matrixTwoForm_mul_neg
#print axioms matrixTwoForm_adjugate
#print axioms twoByTwo_exp_det_one_of_trace_zero
#print axioms sourcePlusIColorMatrix_det_one
#print axioms sourcePlusIColorMatrix_mem_specialUnitary
#print axioms sourcePlusIGaugeCurve_coe
#print axioms sourcePlusIGaugeCurve_one
#print axioms sourcePlusIGaugeCurve_adjointCoefficient_deriv
#check @sourcePlusIGaugeCurve_adjointCoefficient_deriv

end
end FCP.BFSSSU2PhysicalDomainL6G6X
