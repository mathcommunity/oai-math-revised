import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1ESourceRelativeGaugeCharacterReductionProbe

/-!
S1F: genuine source +i SU2 gauge curve halving/inversion.
EXACT original sourcePlusIGaugeCurve and actual pairedAlgebraData.color,
not an abstract replacement curve or surrogate gauge action.

The exponential of identical bounded color matrices combines by
NormedSpace.exp_add_of_commute; these two source group identities will
discharge S1E's half-parameter premises for BOTH z and y curves.
Inverse-conjugation identities remain distinct OPEN concrete obligations.
No Spin(48) manuscript intertwiner or spectral claim is constructed.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000

namespace FCP.BFSSSU2PhysicalDomainS1F
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainS1E

/-- Exact half parameter multiplication for each original positive-i
source SU2 color generator, with no continuity or abstract curve axioms. -/
theorem original_source_curve_half (c : ColorIndex 2) (t : ℝ) :
    sourcePlusIGaugeCurve c (t / 2) *
      sourcePlusIGaugeCurve c (t / 2) =
        sourcePlusIGaugeCurve c t := by
  apply Subtype.ext
  let : NormedAlgebra ℚ (ColorMatrix 2) :=
    .restrictScalars ℚ ℂ (ColorMatrix 2)
  let W : ColorMatrix 2 := (Complex.I : ℂ) • pairedAlgebraData.color c
  change NormedSpace.exp ((t / 2) • W) *
    NormedSpace.exp ((t / 2) • W) =
      NormedSpace.exp (t • W)
  rw [← NormedSpace.exp_add_of_commute
    (Commute.refl ((t / 2) • W))]
  congr 1
  rw [← add_smul]
  congr 1
  ring

/-- Exact inverse identity for the literal original positive-i
source gauge curve. -/
theorem original_source_curve_neg_eq_inv (c : ColorIndex 2) (t : ℝ) :
    sourcePlusIGaugeCurve c (-t) =
      (sourcePlusIGaugeCurve c t)⁻¹ := by
  have hprod : sourcePlusIGaugeCurve c t *
      sourcePlusIGaugeCurve c (-t) = 1 := by
    apply Subtype.ext
    let : NormedAlgebra ℚ (ColorMatrix 2) :=
      .restrictScalars ℚ ℂ (ColorMatrix 2)
    let W : ColorMatrix 2 := (Complex.I : ℂ) • pairedAlgebraData.color c
    change NormedSpace.exp (t • W) *
      NormedSpace.exp ((-t) • W) = 1
    rw [neg_smul]
    rw [← NormedSpace.exp_add_of_commute
      (Commute.refl (t • W)).neg_right]
    simp
  calc
    sourcePlusIGaugeCurve c (-t) =
      (sourcePlusIGaugeCurve c t)⁻¹ *
        (sourcePlusIGaugeCurve c t * sourcePlusIGaugeCurve c (-t)) := by
          simp [mul_assoc]
    _ = (sourcePlusIGaugeCurve c t)⁻¹ := by rw [hprod]; simp

theorem original_source_z_half (t : ℝ) :
    sourceZ (t / 2) * sourceZ (t / 2) = sourceZ t := by
  exact original_source_curve_half (2 : Fin 3) t

theorem original_source_y_half (t : ℝ) :
    sourceY (t / 2) * sourceY (t / 2) = sourceY t := by
  exact original_source_curve_half (1 : Fin 3) t

theorem original_source_z_neg_eq_inv (t : ℝ) :
    sourceZ (-t) = (sourceZ t)⁻¹ :=
  original_source_curve_neg_eq_inv (2 : Fin 3) t

theorem original_source_y_neg_eq_inv (t : ℝ) :
    sourceY (-t) = (sourceY t)⁻¹ :=
  original_source_curve_neg_eq_inv (1 : Fin 3) t

#print axioms original_source_curve_half
#print axioms original_source_curve_neg_eq_inv
#print axioms original_source_z_half
#print axioms original_source_y_half
#print axioms original_source_z_neg_eq_inv
#print axioms original_source_y_neg_eq_inv

end
end FCP.BFSSSU2PhysicalDomainS1F
