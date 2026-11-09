import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7ROriginalSourceInfinitesimalGaugeDefectProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4JExactGaugeDataAssemblyProbe

/-!
L6G7S — original, actually invariant SmoothCore has zero infinitesimal
SU(2) Gauss-equivariance defect on the pinned BFSS boson/Fock types.

NO extra invariance axiom: the states belong to the literal original
pairedGaugeData.invariantCore := physicalSpace.comap coreToL2.
The source GaugeCore.invariantCore_equivariant theorem gives their
forward finite-time equivariance; the independently accepted
L6G7R derivative gives the exact original orbital/current expression.

Neither a new physical subspace, an L² unbounded-generator derivative,
nor a spectral or essential-selfadjointness conclusion is asserted.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace FCP.BFSSSU2PhysicalDomainL6G7S
noncomputable section
open scoped BigOperators

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG2A
open FCP.BFSSSU2GaugeG4B
open FCP.BFSSSU2GaugeG4E
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6G6K
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7R

/-- The defect is *literally zero* for actual source invariant-core
states, because the exact six-field original GaugeData has genuine
G2A bosonic and G4E/G4B fermionic actions. -/
private theorem actualInvariantCore_gaugeDefect_zero
    (c : ColorIndex 2) (f : pairedGaugeData.invariantCore)
    (x : Boson 2) (t : ℝ) :
    f.val (bosonGauge (sourcePlusIGaugeCurve c t) x) -
      fermionGaugeLinearEquiv (sourcePlusIGaugeCurve c t) (f.val x) = 0 := by
  apply sub_eq_zero.mpr
  have h := pairedGaugeData.invariantCore_equivariant f
    (sourcePlusIGaugeCurve c t) x
  change f.val (bosonGauge (sourcePlusIGaugeCurve c t) x) =
    fermionGaugeLinearEquiv (sourcePlusIGaugeCurve c t) (f.val x) at h
  exact h

/-- Actual source physical invariant smooth states annihilate the
exact infinitesimal original orbital-minus-fermion gauge defect.
The source -i gaugeTangent and the +i SU(2) curve carry the formally
qualified relative negative sign. -/
theorem actualInvariantCore_originalSignedGaussDefect_zero
    (c : ColorIndex 2) (f : pairedGaugeData.invariantCore)
    (x : Boson 2) :
    (-(fderiv ℝ (f.val : Boson 2 → Fermion 2) x
        (pairedAlgebraData.gaugeTangent x
          (EuclideanSpace.single c (1 : ℝ)))) -
      sourceFiberFermionColorGenerator pairedAlgebraData c (f.val x)) = 0 := by
  have hcurve :
      (fun t : ℝ =>
        f.val (bosonGauge (sourcePlusIGaugeCurve c t) x) -
          fermionGaugeLinearEquiv (sourcePlusIGaugeCurve c t) (f.val x)) =
      (fun _ : ℝ => (0 : Fermion 2)) := by
    funext t
    exact actualInvariantCore_gaugeDefect_zero c f x t
  have hderiv :=
    originalSmoothCore_gaugeEquivarianceDefect_derivative_zero c f.val x
  rw [hcurve] at hderiv
  exact hderiv.unique (hasDerivAt_const 0 (0 : Fermion 2))

/-- The genuine original invariant core also satisfies the EXACT
right-ordered finite coefficient/position/coordinateDerivative
identity, with the separately qualified original bounded Fock
fermion-current generator. No domain replacement or new axiom. -/
theorem actualInvariantCore_originalCoordinateGaussDefect_zero
    (c : ColorIndex 2) (f : pairedGaugeData.invariantCore)
    (x : Boson 2) :
    ((∑ p : SpaceIndex × ColorIndex 2,
      (∑ A : ColorIndex 2,
        pairedAlgebraData.structureConstant p.2 A c * x (p.1,A)) •
          ((coordinateDerivative (N := 2) p.1 p.2 f.val) x)) -
      sourceFiberFermionColorGenerator pairedAlgebraData c (f.val x)) = 0 := by
  have hcurve :
      (fun t : ℝ =>
        f.val (bosonGauge (sourcePlusIGaugeCurve c t) x) -
          fermionGaugeLinearEquiv (sourcePlusIGaugeCurve c t) (f.val x)) =
      (fun _ : ℝ => (0 : Fermion 2)) := by
    funext t
    exact actualInvariantCore_gaugeDefect_zero c f x t
  have hderiv :=
    originalSmoothCore_gaugeEquivarianceDefect_coordinate_derivative_zero c f.val x
  rw [hcurve] at hderiv
  exact hderiv.unique (hasDerivAt_const 0 (0 : Fermion 2))

#print axioms actualInvariantCore_originalSignedGaussDefect_zero
#print axioms actualInvariantCore_originalCoordinateGaussDefect_zero
#check @actualInvariantCore_originalSignedGaussDefect_zero
#check @actualInvariantCore_originalCoordinateGaussDefect_zero

end
end FCP.BFSSSU2PhysicalDomainL6G7S
