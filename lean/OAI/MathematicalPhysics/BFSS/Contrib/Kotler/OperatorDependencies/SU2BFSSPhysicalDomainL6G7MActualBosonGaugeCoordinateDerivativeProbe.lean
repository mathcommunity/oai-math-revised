import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7CAllTimeNativeColorDerivativeProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG2ABosonGaugeProbe

/-!
L6G7M — first variation of the ORIGINAL SU(2) bosonic configuration
representation on actual 27 real coordinates of Boson 2.

Reuse source-verified +i SU(2) adjointCoefficient tangent
with row B OUTPUT, column A INPUT. G2A is the independently
constructed real-linear, isometric original gaugeConjugate action.

This is a finite-dimensional configuration derivative, not the
differentiation of a gauge PULLBACK on SmoothCore/FullL2.
No unbounded Gauss operator or derivative-domain identification
is asserted; those require independent signed chain-rule proofs.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace FCP.BFSSSU2PhysicalDomainL6G7M
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG2A
open FCP.BFSSSU2PhysicalDomainL6G6X

/-- ORIGINAL bosonGauge, literal source color coefficients, no
replacement SO(3) representation and no index-orientation assumption. -/
theorem actualBosonGauge_coordinate_color_sum
    (g : GaugeGroup 2) (x : Boson 2)
    (i : SpaceIndex) (B : ColorIndex 2) :
    (bosonGauge g x) (i,B) =
      ∑ A : ColorIndex 2,
        pairedAlgebraData.adjointCoefficient g A B * x (i,A) := by
  change
    (pairedAlgebraData.colorConjugate (g : ColorMatrix 2)
      (spatialColor x i)) B =
    ∑ A : ColorIndex 2,
      pairedAlgebraData.adjointCoefficient g A B *
        (spatialColor x i) A
  exact pairedAlgebraData.colorConjugate_coefficient g (spatialColor x i) B

/-- The actual 27-coordinate bosonic SU(2) configuration action
has source-exact +i tangent at the identity:
d/dt x_(i,B) = sum_A f_(B A c) x_(i,A).
This result itself asserts no differentiation on FullL2. -/
theorem actualBosonGauge_coordinate_derivative_zero
    (c : ColorIndex 2) (x : Boson 2)
    (i : SpaceIndex) (B : ColorIndex 2) :
    HasDerivAt
      (fun t : ℝ => (bosonGauge (sourcePlusIGaugeCurve c t) x) (i,B))
      (∑ A : ColorIndex 2,
        pairedAlgebraData.structureConstant B A c * x (i,A))
      0 := by
  have heq :
      (fun t : ℝ => (bosonGauge (sourcePlusIGaugeCurve c t) x) (i,B)) =
      (fun t : ℝ => ∑ A : ColorIndex 2,
        pairedAlgebraData.adjointCoefficient
          (sourcePlusIGaugeCurve c t) A B * x (i,A)) := by
    funext t
    exact actualBosonGauge_coordinate_color_sum
      (sourcePlusIGaugeCurve c t) x i B
  rw [heq]
  apply HasDerivAt.fun_sum
  intro A _
  exact (sourcePlusIGaugeCurve_adjointCoefficient_deriv c A B).mul_const (x (i,A))

#print axioms actualBosonGauge_coordinate_color_sum
#print axioms actualBosonGauge_coordinate_derivative_zero
#check @actualBosonGauge_coordinate_derivative_zero

end
end FCP.BFSSSU2PhysicalDomainL6G7M
