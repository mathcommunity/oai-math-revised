import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7QOriginalSourceGaugeTangentSignProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7LActualGaugeFermionDerivativeProbe

/-!
L6G7R — the exact first variation of the ORIGINAL BFSS smooth-core
pointwise Gauss-equivariance defect along the native +i SU2 curve.

The source physical condition compares f(G.boson g x) with
G.fermion g (f x). Independently qualified Q (original boson tangent
sign) and L (actual original exterior-Fock fermion gauge derivative)
therefore calculate the derivative of their difference.

This theorem holds for ANY original SmoothCore 2 function, not
only invariant ones; the defect need not vanish. The result is
pointwise finite-dimensional calculus and is NOT yet a theorem of
vanishing Gauss charge, closed unbounded L2 generators, or BFSS
spectral results. It introduces NO unsupported invariance premise.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace FCP.BFSSSU2PhysicalDomainL6G7R
noncomputable section
open scoped BigOperators

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG2A
open FCP.BFSSSU2GaugeG4B
open FCP.BFSSSU2PhysicalDomainL6G6K
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7L
open FCP.BFSSSU2PhysicalDomainL6G7N
open FCP.BFSSSU2PhysicalDomainL6G7P
open FCP.BFSSSU2PhysicalDomainL6G7Q

/-- Exact original +i source group: boson pullback minus genuine
Fock-unitary fiber action, differentiated at the identity. The
bosonic term is MINUS original gaugeTangent due to the proven
Q sign theorem, while fermion uses its original bounded current. -/
theorem originalSmoothCore_gaugeEquivarianceDefect_derivative_zero
    (c : ColorIndex 2) (f : SmoothCore 2) (x : Boson 2) :
    HasDerivAt
      (fun t : ℝ =>
        f (bosonGauge (sourcePlusIGaugeCurve c t) x) -
          fermionGaugeLinearEquiv (sourcePlusIGaugeCurve c t) (f x))
      (-(fderiv ℝ (f : Boson 2 → Fermion 2) x
          (pairedAlgebraData.gaugeTangent x
            (EuclideanSpace.single c (1 : ℝ)))) -
        sourceFiberFermionColorGenerator pairedAlgebraData c (f x))
      0 := by
  exact
    (actualBosonGauge_smoothCore_pullback_neg_originalGaugeTangent c f x).sub
      (actualGaugeFermion_derivative_zero c (f x))

/-- The same genuine original source Gauss-equivariance defect,
now in the exact right-ordered finite coordinateDerivative form.
No commuting source coefficient past a derivative occurs. -/
theorem originalSmoothCore_gaugeEquivarianceDefect_coordinate_derivative_zero
    (c : ColorIndex 2) (f : SmoothCore 2) (x : Boson 2) :
    HasDerivAt
      (fun t : ℝ =>
        f (bosonGauge (sourcePlusIGaugeCurve c t) x) -
          fermionGaugeLinearEquiv (sourcePlusIGaugeCurve c t) (f x))
      ((∑ p : SpaceIndex × ColorIndex 2,
        (∑ A : ColorIndex 2,
          pairedAlgebraData.structureConstant p.2 A c * x (p.1,A)) •
            ((coordinateDerivative (N := 2) p.1 p.2 f) x)) -
        sourceFiberFermionColorGenerator pairedAlgebraData c (f x))
      0 := by
  exact
    (actualBosonGauge_smoothCore_pullback_coordinate_derivative_zero c f x).sub
      (actualGaugeFermion_derivative_zero c (f x))

#print axioms originalSmoothCore_gaugeEquivarianceDefect_derivative_zero
#print axioms originalSmoothCore_gaugeEquivarianceDefect_coordinate_derivative_zero
#check @originalSmoothCore_gaugeEquivarianceDefect_derivative_zero
#check @originalSmoothCore_gaugeEquivarianceDefect_coordinate_derivative_zero

end
end FCP.BFSSSU2PhysicalDomainL6G7R
