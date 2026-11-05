import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7POriginalSmoothCoreCoordinateGaugeGeneratorProbe
import OAI.MathematicalPhysics.BFSS.NormalLinearization

/-!
L6G7Q — source-exact sign bridge between the qualified +i gauge
pullback tangent and the pinned original AlgebraData.gaugeTangent.

The pinned source gaugeTangent x w is colorLie w (spatialColor x i),
whereas the already qualified native +i coefficient derivative is
structureConstant B A c * x_(i,A) = colorLie x_i e_c at output B.
The ORIGINAL source colorLie_swap fixes their sign. Neither the
gauge curve convention nor the original orbital generator is altered.

This is a finite vector and pointwise SmoothCore derivative identity.
No closed L² generator, physical Gauss constraint, or spectral claim.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace FCP.BFSSSU2PhysicalDomainL6G7Q
noncomputable section
open scoped BigOperators

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG2A
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7N
open FCP.BFSSSU2PhysicalDomainL6G7O
open FCP.BFSSSU2PhysicalDomainL6G7P

/-- The source color bracket of a spatial configuration with the
native basis color vector has the EXACT original +i coefficient. -/
private theorem sourceColorLie_right_single_component
    (c : ColorIndex 2) (x : Boson 2)
    (i : SpaceIndex) (B : ColorIndex 2) :
    (pairedAlgebraData.colorLie (spatialColor x i)
      (EuclideanSpace.single c (1 : ℝ))) B =
      ∑ A : ColorIndex 2,
        pairedAlgebraData.structureConstant B A c * x (i,A) := by
  change (∑ A : ColorIndex 2, ∑ C : ColorIndex 2,
      pairedAlgebraData.structureConstant B A C * x (i,A) *
        (EuclideanSpace.single c (1 : ℝ)) C) = _
  simp [EuclideanSpace.single_apply]

/-- Exact sign relation to the ORIGINAL source gaugeTangent, whose
Lie bracket has the basis color direction in its FIRST slot.
The +i SU2 group curve differentiates with the opposite sign. -/
theorem sourceBosonGaugeTangent_eq_neg_originalGaugeTangent
    (c : ColorIndex 2) (x : Boson 2) :
    sourceBosonGaugeTangent c x =
      -pairedAlgebraData.gaugeTangent x (EuclideanSpace.single c (1 : ℝ)) := by
  ext p
  rcases p with ⟨i,B⟩
  calc
    sourceBosonGaugeTangent c x (i,B) =
        (pairedAlgebraData.colorLie (spatialColor x i)
          (EuclideanSpace.single c (1 : ℝ))) B := by
            rw [sourceBosonGaugeTangent_apply]
            exact (sourceColorLie_right_single_component c x i B).symm
    _ = -(pairedAlgebraData.colorLie (EuclideanSpace.single c (1 : ℝ))
          (spatialColor x i)) B := by
            simpa only [PiLp.neg_apply] using
              congrArg (fun z : ColorVector 2 => z B)
                (pairedAlgebraData.colorLie_swap (spatialColor x i)
                  (EuclideanSpace.single c (1 : ℝ)))
    _ = (-pairedAlgebraData.gaugeTangent x
          (EuclideanSpace.single c (1 : ℝ))) (i,B) := rfl

/-- Original source SmoothCore forward pullback derivative, now
identified with NEGATIVE original gaugeTangent directional derivative.
This is pointwise; no L² differentiability or Gauss-domain claim. -/
theorem actualBosonGauge_smoothCore_pullback_neg_originalGaugeTangent
    (c : ColorIndex 2) (f : SmoothCore 2) (x : Boson 2) :
    HasDerivAt
      (fun t : ℝ => f (bosonGauge (sourcePlusIGaugeCurve c t) x))
      (-(fderiv ℝ (f : Boson 2 → Fermion 2) x
        (pairedAlgebraData.gaugeTangent x (EuclideanSpace.single c (1 : ℝ))))) 0 := by
  simpa only [sourceBosonGaugeTangent_eq_neg_originalGaugeTangent,
    map_neg] using
    actualBosonGauge_smoothCore_pullback_derivative_zero c f x

#print axioms sourceBosonGaugeTangent_eq_neg_originalGaugeTangent
#print axioms actualBosonGauge_smoothCore_pullback_neg_originalGaugeTangent
#check @actualBosonGauge_smoothCore_pullback_neg_originalGaugeTangent

end
end FCP.BFSSSU2PhysicalDomainL6G7Q
