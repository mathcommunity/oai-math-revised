import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1FSourceGaugeCurveHalvingProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8YOriginalSU2ExactSourceEulerFactorizationProbe

/-!
S1G: literal source SU2 relative-character triviality, a new strict
research CANDIDATE until CI kernel-compilation and axiom audit.

Uses original +i color one-parameter curves, Pauli scale, actual 2x2
matrix SU2 group, and qualified Euler decomposition, NOT an abstract
surrogate group or unproved perfectness instance. Proves fixed
quarter-turn source-group witnesses exchanging Z(t)/Z(-t) and
Y(t)/Y(-t), then discharges S1E's remaining source hypotheses.

Important: V and its 48-theta covariance remain EXPLICIT hypotheses.
No independent manuscript Cl48 module, Spin48 lift or spectrum follows.
-/

set_option autoImplicit false
set_option maxHeartbeats 550000
set_option synthInstance.maxHeartbeats 180000

namespace FCP.BFSSSU2PhysicalDomainS1G
noncomputable section

open Matrix
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6H5E8R
open FCP.BFSSSU2PhysicalDomainL6H5E8T
open FCP.BFSSSU2PhysicalDomainL6H5E8Y
open FCP.BFSSSU2PhysicalDomainS1D
open FCP.BFSSSU2PhysicalDomainS1E
open FCP.BFSSSU2PhysicalDomainS1F

/-- The quarter turn is expressed in exact original source Pauli
normalization; the source angle is π/2, not an inserted new scale. -/
def sourceQuarterTurnTime : ℝ := (Real.pi / 2) * Real.sqrt 2

theorem source_quarter_angle :
    sourceYAngle sourceQuarterTurnTime = Real.pi / 2 := by
  unfold sourceYAngle sourceQuarterTurnTime
  calc
    (Real.pi / 2 * Real.sqrt 2) * FCP.BFSSSU2.pauliScale =
        (Real.pi / 2) * (FCP.BFSSSU2.pauliScale * Real.sqrt 2) := by ring
    _ = Real.pi / 2 := by
      rw [FCP.BFSSSU2.pauliScale_mul_sqrt]
      ring

/-- Two exact original source SU2 elements at the source quarter time. -/
theorem source_quarter_y_matrix :
    (sourceY sourceQuarterTurnTime : ColorMatrix 2) =
      !![(0 : ℂ), 1; -1, 0] := by
  change (sourcePlusIGaugeCurve (1 : Fin 3) sourceQuarterTurnTime : ColorMatrix 2) = _
  rw [source_y_gaugeCurve_real_rotation]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceYRotation, source_quarter_angle,
      Real.cos_pi_div_two, Real.sin_pi_div_two]

theorem source_quarter_z_matrix :
    (sourceZ sourceQuarterTurnTime : ColorMatrix 2) =
      !![Complex.I, 0; 0, -Complex.I] := by
  change (sourcePlusIGaugeCurve (2 : Fin 3) sourceQuarterTurnTime : ColorMatrix 2) = _
  rw [source_z_gaugeCurve_diagonal_exp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceZDiagonal_exp_zero,
      sourceZDiagonal_exp_one, source_quarter_angle,
      Real.cos_pi_div_two, Real.sin_pi_div_two]

theorem source_z_diag_neg_zero (t : ℝ) :
    sourceZDiagonal (-t) (0 : Fin 2) =
      sourceZDiagonal t (1 : Fin 2) := by
  simp [sourceZDiagonal]

theorem source_z_diag_neg_one (t : ℝ) :
    sourceZDiagonal (-t) (1 : Fin 2) =
      sourceZDiagonal t (0 : Fin 2) := by
  simp [sourceZDiagonal]

theorem source_y_angle_neg (t : ℝ) :
    sourceYAngle (-t) = -sourceYAngle t := by
  simp [sourceYAngle]

/-- Actual group equality, proved at the underlying literal source
SU2 2x2 matrices with the 2 independent diagonal-entry identities. -/
theorem original_source_yquarter_z_swap (t : ℝ) :
    sourceY sourceQuarterTurnTime * sourceZ t =
      sourceZ (-t) * sourceY sourceQuarterTurnTime := by
  apply Subtype.ext
  change (sourceY sourceQuarterTurnTime : ColorMatrix 2) *
      (sourceZ t : ColorMatrix 2) =
    (sourceZ (-t) : ColorMatrix 2) *
      (sourceY sourceQuarterTurnTime : ColorMatrix 2)
  rw [source_quarter_y_matrix]
  change (!![(0 : ℂ), 1; -1, 0] : ColorMatrix 2) *
    (sourcePlusIGaugeCurve (2 : Fin 3) t : ColorMatrix 2) =
    (sourcePlusIGaugeCurve (2 : Fin 3) (-t) : ColorMatrix 2) *
    (!![(0 : ℂ), 1; -1, 0] : ColorMatrix 2)
  rw [source_z_gaugeCurve_diagonal_exp,
    source_z_gaugeCurve_diagonal_exp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply,
      source_z_diag_neg_zero, source_z_diag_neg_one]

theorem original_source_zquarter_y_swap (t : ℝ) :
    sourceZ sourceQuarterTurnTime * sourceY t =
      sourceY (-t) * sourceZ sourceQuarterTurnTime := by
  apply Subtype.ext
  change (sourceZ sourceQuarterTurnTime : ColorMatrix 2) *
      (sourceY t : ColorMatrix 2) =
    (sourceY (-t) : ColorMatrix 2) *
      (sourceZ sourceQuarterTurnTime : ColorMatrix 2)
  rw [source_quarter_z_matrix]
  change (!![Complex.I, 0; 0, -Complex.I] : ColorMatrix 2) *
    (sourcePlusIGaugeCurve (1 : Fin 3) t : ColorMatrix 2) =
    (sourcePlusIGaugeCurve (1 : Fin 3) (-t) : ColorMatrix 2) *
    (!![Complex.I, 0; 0, -Complex.I] : ColorMatrix 2)
  rw [source_y_gaugeCurve_real_rotation,
    source_y_gaugeCurve_real_rotation]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceYRotation, source_y_angle_neg, Real.cos_neg,
      Real.sin_neg, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

theorem original_source_z_flip (t : ℝ) :
    ∃ k : GaugeGroup 2,
      k * sourceZ t * k⁻¹ = (sourceZ t)⁻¹ := by
  refine ⟨sourceY sourceQuarterTurnTime, ?_⟩
  calc
    sourceY sourceQuarterTurnTime * sourceZ t *
        (sourceY sourceQuarterTurnTime)⁻¹ =
      sourceZ (-t) *
        (sourceY sourceQuarterTurnTime *
          (sourceY sourceQuarterTurnTime)⁻¹) := by
            rw [original_source_yquarter_z_swap t, mul_assoc]
    _ = (sourceZ t)⁻¹ := by
      rw [mul_inv_cancel, mul_one, original_source_z_neg_eq_inv]

theorem original_source_y_flip (t : ℝ) :
    ∃ k : GaugeGroup 2,
      k * sourceY t * k⁻¹ = (sourceY t)⁻¹ := by
  refine ⟨sourceZ sourceQuarterTurnTime, ?_⟩
  calc
    sourceZ sourceQuarterTurnTime * sourceY t *
        (sourceZ sourceQuarterTurnTime)⁻¹ =
      sourceY (-t) *
        (sourceZ sourceQuarterTurnTime *
          (sourceZ sourceQuarterTurnTime)⁻¹) := by
            rw [original_source_zquarter_y_swap t, mul_assoc]
    _ = (sourceY t)⁻¹ := by
      rw [mul_inv_cancel, mul_one, original_source_y_neg_eq_inv]

/-- Fully source-exact character triviality: this theorem needs NO
separate curve hypothesis, but DOES require the candidate V's actual
48-generator color covariance and homomorphism on the source Fermion 2. -/
theorem original_relativeGaugeScalar_trivial
    (V : GaugeGroup 2 →* (Fermion 2 ≃ₗ[ℂ] Fermion 2))
    (hV : ∀ (g : GaugeGroup 2) (α : SpinIndex)
      (A : ColorIndex 2) (v : Fermion 2),
      V g (pairedTheta α A v) =
        ∑ B : ColorIndex 2,
          (pairedAlgebraData.adjointCoefficient g A B : ℂ) •
            pairedTheta α B (V g v))
    (g : GaugeGroup 2) :
    relativeGaugeScalar V hV g = 1 := by
  exact original_relativeGaugeScalar_one_of_curve_relations
    V hV original_source_z_flip original_source_y_flip
    original_source_z_half original_source_y_half
    original_source_zyz_exists g

#print axioms source_quarter_angle
#print axioms source_quarter_y_matrix
#print axioms source_quarter_z_matrix
#print axioms source_z_diag_neg_zero
#print axioms source_z_diag_neg_one
#print axioms source_y_angle_neg
#print axioms original_source_yquarter_z_swap
#print axioms original_source_zquarter_y_swap
#print axioms original_source_z_flip
#print axioms original_source_y_flip
#print axioms original_relativeGaugeScalar_trivial

end
end FCP.BFSSSU2PhysicalDomainS1G
