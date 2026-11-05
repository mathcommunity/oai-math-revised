import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6UOriginalAdjointColorTangentProbe
import OAI.MathematicalPhysics.BFSS.GaugeGeometry

/-!
L6G6V — exact source +i color-conjugation matrix derivative.

Reuse the pinned BFSSGaugeFlow.exp_conj_deriv_zero rather than
rebuilding matrix exponential calculus. The result gives the genuine
matrix-valued first variation, with the ORIGINAL paired color
matrices and +i convention used in L6G6U. It also proves unitarity
of this ambient matrix curve.

Boundary: membership in the SPECIAL unitary group, the derivative of
the exact adjointCoefficient on GaugeGroup 2, and the derivative of
the exterior/Fock representation are separate open obligations.
Do not treat ambient unitarity as SU(2) membership or as a Gauss proof.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G6V
noncomputable section

open Matrix
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A

/-- The correctly oriented +i curve on original color matrices.
No SU2 membership is asserted by the definition. -/
noncomputable def sourcePlusIColorMatrix (c : ColorIndex 2)
    (t : ℝ) : ColorMatrix 2 :=
  NormedSpace.exp
    (t • ((Complex.I : ℂ) • pairedAlgebraData.color c))

theorem sourcePlusIColorMatrix_one (c : ColorIndex 2) :
    sourcePlusIColorMatrix c 0 = 1 := by
  simp [sourcePlusIColorMatrix]

/-- The actual +i matrix-exponential curve is unitary.
This is not yet the separate determinant-one SU2 obligation. -/
theorem sourcePlusIColorMatrix_unitary
    (c : ColorIndex 2) (t : ℝ) :
    sourcePlusIColorMatrix c t ∈ unitary (ColorMatrix 2) := by
  have h :=
    OAI.BFSSGaugeFlow.exp_skew
      (-pairedAlgebraData.color c)
      (pairedAlgebraData.color_hermitian c).neg t
  simpa only [sourcePlusIColorMatrix, smul_neg,
    neg_smul, neg_neg] using h

/-- Differentiation of the ACTUAL exponentiated color matrix
conjugation in the positive-i convention. This is not a derivative
on GaugeGroup 2 until determinant-one membership is discharged. -/
theorem sourcePlusIConjugation_deriv
    (c A : ColorIndex 2) :
    HasDerivAt
      (fun t : ℝ =>
        sourcePlusIColorMatrix c t * pairedAlgebraData.color A *
          NormedSpace.exp
            (t • (-((Complex.I : ℂ) • pairedAlgebraData.color c))))
      ((Complex.I : ℂ) •
        (pairedAlgebraData.color c * pairedAlgebraData.color A -
         pairedAlgebraData.color A * pairedAlgebraData.color c)) 0 := by
  have h :
      HasDerivAt
        (fun t : ℝ =>
          sourcePlusIColorMatrix c t * pairedAlgebraData.color A *
            NormedSpace.exp
              (t • (-((Complex.I : ℂ) • pairedAlgebraData.color c))))
        (((Complex.I : ℂ) • pairedAlgebraData.color c) *
             pairedAlgebraData.color A -
         pairedAlgebraData.color A *
           ((Complex.I : ℂ) • pairedAlgebraData.color c)) 0 :=
    OAI.BFSSGaugeFlow.exp_conj_deriv_zero
      ((Complex.I : ℂ) • pairedAlgebraData.color c)
      (pairedAlgebraData.color A)
  have heq :
      ((Complex.I : ℂ) • pairedAlgebraData.color c) *
          pairedAlgebraData.color A -
        pairedAlgebraData.color A *
          ((Complex.I : ℂ) • pairedAlgebraData.color c) =
        (Complex.I : ℂ) •
          (pairedAlgebraData.color c * pairedAlgebraData.color A -
           pairedAlgebraData.color A * pairedAlgebraData.color c) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_sub]
  rw [heq] at h
  exact h

/-- The same proved derivative, in the EXACT pinned Hermitian
source-bracket convention -i[X,Y]. This is a sign check, not a
renaming of a hypothetical gauge-representation derivative. -/
theorem sourcePlusIConjugation_sourceBracket_deriv
    (c A : ColorIndex 2) :
    HasDerivAt
      (fun t : ℝ =>
        sourcePlusIColorMatrix c t * pairedAlgebraData.color A *
          NormedSpace.exp
            (t • (-((Complex.I : ℂ) • pairedAlgebraData.color c))))
      (-(AlgebraData.bracket
        (pairedAlgebraData.color c)
        (pairedAlgebraData.color A))) 0 := by
  have h := sourcePlusIConjugation_deriv c A
  have heq :
      (Complex.I : ℂ) •
          (pairedAlgebraData.color c * pairedAlgebraData.color A -
           pairedAlgebraData.color A * pairedAlgebraData.color c) =
        -(AlgebraData.bracket
          (pairedAlgebraData.color c)
          (pairedAlgebraData.color A)) := by
    simp only [AlgebraData.bracket, neg_smul, neg_neg]
  rw [heq] at h
  exact h

#print axioms sourcePlusIColorMatrix_one
#print axioms sourcePlusIColorMatrix_unitary
#print axioms sourcePlusIConjugation_deriv
#print axioms sourcePlusIConjugation_sourceBracket_deriv
#check @sourcePlusIConjugation_sourceBracket_deriv

end
end FCP.BFSSSU2PhysicalDomainL6G6V
