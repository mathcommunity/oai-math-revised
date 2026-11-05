import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7OOriginalSmoothCoreGaugePullbackDerivativeProbe

/-!
L6G7P — the exact original coordinate-derivative expression of the
already-qualified forward SU(2) boson pullback tangent on SmoothCore 2.

Use the pinned EuclideanSpace canonical orthonormal basis to expand
the source Boson 2 vector tangent, then transport through the exact
original Fréchet derivative and upstream coordinateDerivative_apply.
This is the actual source structureConstant B A c, position x_(i,A),
and original coordinateDerivative_(i,B), with no surrogate operator.

This remains an equality of pointwise derivatives of test functions;
no claim concerning an unbounded L² infinitesimal generator, a
closed Gauss constraint, or BFSS spectral theory.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace FCP.BFSSSU2PhysicalDomainL6G7P
noncomputable section
open scoped BigOperators

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG2A
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7N
open FCP.BFSSSU2PhysicalDomainL6G7O

/-- The true source bosonic gauge tangent acts on any original
SmoothCore function as a right-ordered finite combination of the
original source coordinateDerivative operators. -/
theorem originalSmoothCore_colorTangent_fderiv_coordinate_sum
    (c : ColorIndex 2) (f : SmoothCore 2) (x : Boson 2) :
    fderiv ℝ (f : Boson 2 → Fermion 2) x
      (sourceBosonGaugeTangent c x) =
      ∑ p : SpaceIndex × ColorIndex 2,
        (∑ A : ColorIndex 2,
          pairedAlgebraData.structureConstant p.2 A c * x (p.1,A)) •
            ((coordinateDerivative (N := 2) p.1 p.2 f) x) := by
  -- Exact canonical orthonormal-basis reconstruction, not a new
  -- EuclideanSpace/ordinary Pi additive or normed instance.
  have hbasis :
      (∑ p : SpaceIndex × ColorIndex 2,
        (sourceBosonGaugeTangent c x p) • EuclideanSpace.single p (1 : ℝ)) =
        sourceBosonGaugeTangent c x := by
    simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (SpaceIndex × ColorIndex 2) ℝ).sum_repr
        (sourceBosonGaugeTangent c x)
  calc
    _ = fderiv ℝ (f : Boson 2 → Fermion 2) x
          (∑ p : SpaceIndex × ColorIndex 2,
            (sourceBosonGaugeTangent c x p) •
              EuclideanSpace.single p (1 : ℝ)) := by rw [hbasis]
    _ = ∑ p : SpaceIndex × ColorIndex 2,
          (sourceBosonGaugeTangent c x p) •
            (fderiv ℝ (f : Boson 2 → Fermion 2) x
              (EuclideanSpace.single p (1 : ℝ))) := by
            rw [map_sum]
            simp only [map_smul]
    _ = ∑ p : SpaceIndex × ColorIndex 2,
          (sourceBosonGaugeTangent c x p) •
            ((coordinateDerivative (N := 2) p.1 p.2 f) x) := by
            apply Finset.sum_congr rfl
            intro p _
            rw [coordinateDerivative_apply]
    _ = ∑ p : SpaceIndex × ColorIndex 2,
          (∑ A : ColorIndex 2,
            pairedAlgebraData.structureConstant p.2 A c * x (p.1,A)) •
              ((coordinateDerivative (N := 2) p.1 p.2 f) x) := by
            apply Finset.sum_congr rfl
            intro p _
            rcases p with ⟨i,B⟩
            rw [sourceBosonGaugeTangent_apply]

/-- Derivative of the actual original forward source bosonic pullback,
with the complete literal right-ordered finite color/position/derivative
coefficient expression. No inverse convention or unsupported Gauss
operator domain identification is introduced. -/
theorem actualBosonGauge_smoothCore_pullback_coordinate_derivative_zero
    (c : ColorIndex 2) (f : SmoothCore 2) (x : Boson 2) :
    HasDerivAt
      (fun t : ℝ => f (bosonGauge (sourcePlusIGaugeCurve c t) x))
      (∑ p : SpaceIndex × ColorIndex 2,
        (∑ A : ColorIndex 2,
          pairedAlgebraData.structureConstant p.2 A c * x (p.1,A)) •
            ((coordinateDerivative (N := 2) p.1 p.2 f) x)) 0 := by
  simpa only [originalSmoothCore_colorTangent_fderiv_coordinate_sum c f x] using
    actualBosonGauge_smoothCore_pullback_derivative_zero c f x

#print axioms originalSmoothCore_colorTangent_fderiv_coordinate_sum
#print axioms actualBosonGauge_smoothCore_pullback_coordinate_derivative_zero
#check @actualBosonGauge_smoothCore_pullback_coordinate_derivative_zero

end
end FCP.BFSSSU2PhysicalDomainL6G7P
