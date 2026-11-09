import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6XOriginalSU2GaugeCurveProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG3AAdjointColorRepresentationProbe

/-!
L6G7B — finite-time group law for the ACTUAL original +i color SU(2)
curve, followed by the exact all-time color-coefficient composition
law. This module does not invoke any Fock operator or the unqualified
L6G7A derivative wrapper.

Source: g_c(t) = exp(t * i * pairedAlgebraData.color c) in the literal
GaugeGroup 2; matrix rows B are output colors, columns A input colors.
Scientific boundary: this is the native SU(2)/color-matrix group law,
not yet an all-time derivative of R, finite-time Fock covariance,
gauge-generator equality or BFSS spectrum.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace FCP.BFSSSU2PhysicalDomainL6G7B
noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG3A
open FCP.BFSSSU2PhysicalDomainL6G6V
open FCP.BFSSSU2PhysicalDomainL6G6X

private abbrev SourceColorEnd := ColorMatrix 2

local instance sourceColorRationalNormedAlgebra :
    NormedAlgebra ℚ SourceColorEnd :=
  .restrictScalars ℚ ℂ SourceColorEnd

/-- The exact source +i matrix exponential has the one-parameter
group law. Complex scalar transport is only a proof interface:
the original real-time source curve is not redefined. -/
theorem sourcePlusIColorMatrix_add (c : ColorIndex 2) (s t : ℝ) :
    sourcePlusIColorMatrix c (s+t) =
      sourcePlusIColorMatrix c s * sourcePlusIColorMatrix c t := by
  change NormedSpace.exp (((s+t : ℝ) : ℂ) •
      ((Complex.I : ℂ) • pairedAlgebraData.color c)) =
    NormedSpace.exp ((s : ℂ) •
      ((Complex.I : ℂ) • pairedAlgebraData.color c)) *
    NormedSpace.exp ((t : ℂ) •
      ((Complex.I : ℂ) • pairedAlgebraData.color c))
  have hadd :
      (((s : ℝ) : ℂ) + ((t : ℝ) : ℂ)) •
        ((Complex.I : ℂ) • pairedAlgebraData.color c) =
      ((s : ℂ) • ((Complex.I : ℂ) • pairedAlgebraData.color c)) +
        ((t : ℂ) • ((Complex.I : ℂ) • pairedAlgebraData.color c)) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply]
    exact add_smul (s : ℂ) (t : ℂ)
      (((Complex.I : ℂ) • pairedAlgebraData.color c) i j)
  rw [Complex.ofReal_add, hadd]
  exact NormedSpace.exp_add_of_commute
    (((Commute.refl ((Complex.I : ℂ) • pairedAlgebraData.color c)).smul_left
      (s : ℂ)).smul_right (t : ℂ))

/-- The exact determinant-one SOURCE curve is a homomorphism of the
additive real parameter into GaugeGroup 2. -/
theorem sourcePlusIGaugeCurve_add (c : ColorIndex 2) (s t : ℝ) :
    sourcePlusIGaugeCurve c (s+t) =
      sourcePlusIGaugeCurve c s * sourcePlusIGaugeCurve c t := by
  apply Subtype.ext
  exact sourcePlusIColorMatrix_add c s t

/-- At every pair of real times, the native original adjoint
coefficients obey the full three-color composition law. All indices
are original: A=input, B=output, D=intermediate. -/
theorem sourceNativeAdjointCoefficient_add
    (c A B : ColorIndex 2) (s t : ℝ) :
    pairedAlgebraData.adjointCoefficient
      (sourcePlusIGaugeCurve c (s+t)) A B =
    ∑ D : ColorIndex 2,
      pairedAlgebraData.adjointCoefficient (sourcePlusIGaugeCurve c s) D B *
        pairedAlgebraData.adjointCoefficient (sourcePlusIGaugeCurve c t) A D := by
  rw [sourcePlusIGaugeCurve_add]
  exact adjointCoefficient_mul
    (sourcePlusIGaugeCurve c s) (sourcePlusIGaugeCurve c t) A B

/-- Native coefficients start exactly at the identity color matrix. -/
theorem sourceNativeAdjointCoefficient_zero
    (c A B : ColorIndex 2) :
    pairedAlgebraData.adjointCoefficient
      (sourcePlusIGaugeCurve c 0) A B =
      if A = B then 1 else 0 := by
  rw [sourcePlusIGaugeCurve_one]
  exact adjointCoefficient_one A B

#print axioms sourcePlusIColorMatrix_add
#print axioms sourcePlusIGaugeCurve_add
#print axioms sourceNativeAdjointCoefficient_add
#print axioms sourceNativeAdjointCoefficient_zero
#check @sourcePlusIGaugeCurve_add
#check @sourceNativeAdjointCoefficient_add

end
end FCP.BFSSSU2PhysicalDomainL6G7B
