import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7MActualBosonGaugeCoordinateDerivativeProbe
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
L6G7N — actual original 27-dimensional bosonic gauge tangent,
not merely 27 disconnected scalar coordinate equations.

The qualified M scalar derivatives are assembled using Mathlib's
exact finite-index continuous linear equivalence from the literal
EuclideanSpace (PiLp 2) to its coordinate Pi function. The tangent
is the original source Lie-bracket/color sum with output B/input A
and +i SU(2) curve convention. No source Fock substitution.

No derivative of gauge pullback on SmoothCore or FullL2, no claim
about generator domains or the combined boson/fermion Gauss operator.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace FCP.BFSSSU2PhysicalDomainL6G7N
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG2A
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7M

/-- Literal original finite 27-coordinate bosonic SU(2) tangent
for the actual G2A gauge action. -/
noncomputable def sourceBosonGaugeTangent
    (c : ColorIndex 2) (x : Boson 2) : Boson 2 :=
  WithLp.toLp 2 (fun p : SpaceIndex × ColorIndex 2 =>
    ∑ A : ColorIndex 2,
      pairedAlgebraData.structureConstant p.2 A c * x (p.1,A))

@[simp] theorem sourceBosonGaugeTangent_apply
    (c : ColorIndex 2) (x : Boson 2)
    (i : SpaceIndex) (B : ColorIndex 2) :
    sourceBosonGaugeTangent c x (i,B) =
      ∑ A : ColorIndex 2,
        pairedAlgebraData.structureConstant B A c * x (i,A) := rfl

/-- Actual source G2A bosonGauge differentiates, AS A VECTOR in the
original Boson 2 Euclidean space, to the source-exact color tangent.
Use the pinned Mathlib PiLp coordinate-derivative equivalence directly;
do not elaborate a second Pi-function normed/module instance. -/
theorem actualBosonGauge_vector_derivative_zero
    (c : ColorIndex 2) (x : Boson 2) :
    HasDerivAt
      (fun t : ℝ => bosonGauge (sourcePlusIGaugeCurve c t) x)
      (sourceBosonGaugeTangent c x) 0 := by
  have hcoord (p : SpaceIndex × ColorIndex 2) :
      HasDerivAt
        (fun t : ℝ => (bosonGauge (sourcePlusIGaugeCurve c t) x) p)
        (sourceBosonGaugeTangent c x p) 0 := by
    rcases p with ⟨i, B⟩
    simpa only [sourceBosonGaugeTangent_apply] using
      actualBosonGauge_coordinate_derivative_zero c x i B
  -- Previous #210–#213 attempts rebuilt a Pi-space derivative and
  -- encountered incompatible elaborated Pi module/additive instances
  -- when transporting it back through a continuous linear equivalence.
  -- Here the codomain remains the ORIGINAL PiLp 2 at every step.
  rw [hasDerivAt_iff_hasFDerivAt, ← hasFDerivWithinAt_univ]
  apply (hasFDerivWithinAt_piLp (p := 2)).mpr
  intro p
  simpa only [ContinuousLinearMap.comp_toSpanSingleton, PiLp.proj_apply]
    using (hcoord p).hasFDerivAt.hasFDerivWithinAt

#print axioms sourceBosonGaugeTangent_apply
#print axioms actualBosonGauge_vector_derivative_zero
#check @actualBosonGauge_vector_derivative_zero

end
end FCP.BFSSSU2PhysicalDomainL6G7N
