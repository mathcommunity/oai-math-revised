import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7BOriginalPlusIGaugeCurveGroupLawProbe

/-!
L6G7C — all-time derivative of the EXACT original positive-i SU(2)
color adjoint representation, no surrogate matrix or Fock assumption.

G3A gives source R(g*h)=R(g)R(h). L6G7B qualifies the
one-parameter group law of g_c(t), and L6G6X separately qualifies
R'_c(0)[B,A]=f_(B A c). Here we differentiate R(h+t) at h=0
via the finite three-color composition, then transport through
h=(u-t) to obtain the derivative at every literal real t.

No claim about exterior/Fock gauge covariance, gauge-generator
equality, combined Gauss law, charge square, or spectrum.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G7C
noncomputable section

open scoped BigOperators
open Matrix
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG3A
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7B

/-- Exact source structure-constant generator with row/output B
and column/input D, preserving the original positive-i convention. -/
noncomputable def sourceColorGeneratorMatrix (c : ColorIndex 2) :
    Matrix (ColorIndex 2) (ColorIndex 2) ℝ :=
  fun B D => pairedAlgebraData.structureConstant B D c

/-- Every original color coefficient satisfies the all-time evolution.
This is the B,A entry of R'_c(t)=C_c R_c(t). -/
theorem sourceNativeAdjointCoefficient_deriv_all
    (c A B : ColorIndex 2) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ => pairedAlgebraData.adjointCoefficient
        (sourcePlusIGaugeCurve c u) A B)
      (∑ D : ColorIndex 2,
         pairedAlgebraData.structureConstant B D c *
         pairedAlgebraData.adjointCoefficient
           (sourcePlusIGaugeCurve c t) A D) t := by
  have hsum : HasDerivAt
      (fun h : ℝ => ∑ D : ColorIndex 2,
         pairedAlgebraData.adjointCoefficient (sourcePlusIGaugeCurve c h) D B *
           pairedAlgebraData.adjointCoefficient (sourcePlusIGaugeCurve c t) A D)
      (∑ D : ColorIndex 2,
         pairedAlgebraData.structureConstant B D c *
           pairedAlgebraData.adjointCoefficient (sourcePlusIGaugeCurve c t) A D) 0 := by
    apply HasDerivAt.fun_sum
    intro D _
    exact (sourcePlusIGaugeCurve_adjointCoefficient_deriv c D B).mul_const
      (pairedAlgebraData.adjointCoefficient (sourcePlusIGaugeCurve c t) A D)
  have hshift : HasDerivAt
      (fun h : ℝ => pairedAlgebraData.adjointCoefficient
        (sourcePlusIGaugeCurve c (h + t)) A B)
      (∑ D : ColorIndex 2,
         pairedAlgebraData.structureConstant B D c *
           pairedAlgebraData.adjointCoefficient
             (sourcePlusIGaugeCurve c t) A D) 0 := by
    have heq : (fun h : ℝ => pairedAlgebraData.adjointCoefficient
        (sourcePlusIGaugeCurve c (h+t)) A B) =
      (fun h : ℝ => ∑ D : ColorIndex 2,
         pairedAlgebraData.adjointCoefficient (sourcePlusIGaugeCurve c h) D B *
           pairedAlgebraData.adjointCoefficient
             (sourcePlusIGaugeCurve c t) A D) := by
      funext h
      exact sourceNativeAdjointCoefficient_add c A B h t
    rw [heq]
    exact hsum
  -- Specify the inner map and its basepoint equality independently.
  -- In #173, direct .comp inferred (t - ·) from the syntactic t-t
  -- instead of the required (· - t). The vector-space chain rule
  -- with an explicit basepoint equality avoids that ambiguity.
  have hinner : HasDerivAt (fun u : ℝ => u - t) (1 : ℝ) t :=
    (hasDerivAt_id' t).sub_const t
  have hpoint : (0 : ℝ) = (fun u : ℝ => u - t) t := by
    simp only [sub_self]
  have hback := hshift.scomp_of_eq t hinner hpoint
  simpa only [Function.comp_def, sub_add_cancel, one_smul] using hback

/-- The complete three-by-three source color matrix satisfies
R'_c(t)=C_c R_c(t) at EVERY real t, without a new derivative premise. -/
theorem sourceAdjointColorMatrix_deriv_all
    (c : ColorIndex 2) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ => adjointColorMatrix (sourcePlusIGaugeCurve c u))
      (sourceColorGeneratorMatrix c *
        adjointColorMatrix (sourcePlusIGaugeCurve c t)) t := by
  apply hasDerivAt_pi.mpr
  intro B
  apply hasDerivAt_pi.mpr
  intro A
  simpa only [sourceColorGeneratorMatrix, adjointColorMatrix, Matrix.mul_apply] using
    sourceNativeAdjointCoefficient_deriv_all c A B t

#print axioms sourceNativeAdjointCoefficient_deriv_all
#print axioms sourceAdjointColorMatrix_deriv_all
#check @sourceAdjointColorMatrix_deriv_all

end
end FCP.BFSSSU2PhysicalDomainL6G7C
