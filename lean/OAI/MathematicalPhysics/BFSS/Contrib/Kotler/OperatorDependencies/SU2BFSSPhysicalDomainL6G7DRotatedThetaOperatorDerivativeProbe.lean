import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7CAllTimeNativeColorDerivativeProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6ZOriginalColorFlowVacuumProbe
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
L6G7D — source-native all-time differentiated color-rotated Majorana
operator, on the actual original bounded Fermion 2 source.

Use kernel-qualified L6G7C R'(t)=C R(t), scalar extension ℝ→ℂ,
a constant-vector smul derivative, and a finite sum. The Fock
Majorana operators themselves remain LITERAL pairedAlgebraData.theta.
Do not require the unqualified L6G7A pointwise tangent wrapper.

Boundary: this stage differentiates B_A(t)=Σ_B R(t)[B,A] theta_B.
It does NOT YET identify B_A'(t)=[J,B_A(t)], prove full finite-time
covariance, identify the native G4B implementer, or prove Gauss/spectrum.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace FCP.BFSSSU2PhysicalDomainL6G7D
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2PhysicalDomainL6G6K
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7C

/-- The source color-rotated original Majorana operator, with
B=output, A=input, literal theta fields, no proxy space. -/
noncomputable def sourceRotatedTheta (c : ColorIndex 2)
    (spin : SpinIndex) (A : ColorIndex 2) (u : ℝ) : SourceFiberEnd :=
  ∑ B : ColorIndex 2,
    (pairedAlgebraData.adjointCoefficient
      (sourcePlusIGaugeCurve c u) A B : ℂ) •
        pairedAlgebraData.theta spin B

/-- Named formal right-hand side of the differentiated rotated source
operator. Its identification with a commutator is a separate obligation. -/
noncomputable def sourceRotatedThetaDerivative (c : ColorIndex 2)
    (spin : SpinIndex) (A : ColorIndex 2) (t : ℝ) : SourceFiberEnd :=
  ∑ B : ColorIndex 2,
    ((∑ D : ColorIndex 2,
      pairedAlgebraData.structureConstant B D c *
        pairedAlgebraData.adjointCoefficient
          (sourcePlusIGaugeCurve c t) A D : ℝ) : ℂ) •
      pairedAlgebraData.theta spin B

/-- Differentiate one actual color coefficient after casting it to ℂ,
then multiplying the literal bounded Majorana by that scalar. -/
theorem sourceRotatedThetaTerm_deriv_all
    (c : ColorIndex 2) (spin : SpinIndex)
    (A B : ColorIndex 2) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        (pairedAlgebraData.adjointCoefficient
          (sourcePlusIGaugeCurve c u) A B : ℂ) •
            pairedAlgebraData.theta spin B)
      (((∑ D : ColorIndex 2,
         pairedAlgebraData.structureConstant B D c *
         pairedAlgebraData.adjointCoefficient
           (sourcePlusIGaugeCurve c t) A D : ℝ) : ℂ) •
             pairedAlgebraData.theta spin B) t := by
  exact ((sourceNativeAdjointCoefficient_deriv_all c A B t).ofReal_comp).smul_const
    (pairedAlgebraData.theta spin B)

/-- All-time derivative of the exact original bounded-operator
combination B_A(t), purely from the accepted native color ODE. -/
theorem sourceRotatedTheta_deriv_all
    (c : ColorIndex 2) (spin : SpinIndex)
    (A : ColorIndex 2) (t : ℝ) :
    HasDerivAt (fun u : ℝ => sourceRotatedTheta c spin A u)
      (sourceRotatedThetaDerivative c spin A t) t := by
  unfold sourceRotatedTheta sourceRotatedThetaDerivative
  apply HasDerivAt.fun_sum
  intro B _
  exact sourceRotatedThetaTerm_deriv_all c spin A B t

#print axioms sourceRotatedThetaTerm_deriv_all
#print axioms sourceRotatedTheta_deriv_all
#check @sourceRotatedTheta_deriv_all

end
end FCP.BFSSSU2PhysicalDomainL6G7D
