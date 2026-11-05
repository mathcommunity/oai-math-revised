import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5C2OriginalCombinedFockBosonPointwiseDerivativeProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5BOriginalDenseCoreGaussCandidateProbe
import Mathlib.LinearAlgebra.Complex.Module

/-!
H5C3: exact original BFSS source coefficient bridge.
Real forward color coefficient sums and the Complex-linear H5B
SmoothCore candidate act identically on the genuine original
Fermion 2. Thus the ACTUAL H0 combined gauge orbit's pointwise
time-zero derivative equals the original H5B Gauss candidate.
No strong FullL2 differentiability or spectral inference.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000
namespace FCP.BFSSSU2PhysicalDomainL6H5C3
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2PhysicalDomainL6G6K
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6H0
open FCP.BFSSSU2PhysicalDomainL6H5B
open FCP.BFSSSU2PhysicalDomainL6H5C2

theorem actualOriginalColorCoefficient_real_complex_sum_eq
    (c : ColorIndex 2) (f : SmoothCore 2) (x : Boson 2) :
    (∑ p : SpaceIndex × ColorIndex 2,
      (∑ A : ColorIndex 2,
        pairedAlgebraData.structureConstant p.2 A c * x (p.1, A)) •
          ((coordinateDerivative (N := 2) p.1 p.2 f) x)) =
    (∑ p : SpaceIndex × ColorIndex 2, ∑ A : ColorIndex 2,
      ((pairedAlgebraData.structureConstant p.2 A c : ℂ) *
        (x (p.1, A) : ℂ)) •
          ((coordinateDerivative (N := 2) p.1 p.2 f) x)) := by
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro A _
  simp only [← Complex.ofReal_mul, Complex.coe_smul]

theorem actualOriginalCoreColorGaussCandidate_eq_combined_coordinates
    (c : ColorIndex 2) (f : SmoothCore 2) (x : Boson 2) :
    (actualOriginalCoreColorGaussCandidate c f) x =
      sourceFiberFermionColorGenerator pairedAlgebraData c (f x) -
        (∑ p : SpaceIndex × ColorIndex 2,
          (∑ A : ColorIndex 2,
            pairedAlgebraData.structureConstant p.2 A c * x (p.1,A)) •
              ((coordinateDerivative (N := 2) p.1 p.2 f) x)) := by
  rw [actualOriginalCoreColorGaussCandidate_pointwise]
  congr 1
  exact (actualOriginalColorCoefficient_real_complex_sum_eq c f x).symm

theorem actualOriginalSmoothGaugeOrbit_gaussCandidate_pointwise_derivative_zero
    (c : ColorIndex 2) (f : SmoothCore 2) (x : Boson 2) :
    HasDerivAt
      (fun t : ℝ =>
        actualOriginalSmoothGaugeOrbitRepresentative f
          (sourcePlusIGaugeCurve c t) x)
      ((actualOriginalCoreColorGaussCandidate c f) x)
      0 := by
  -- Keep the already-qualified source derivative opaque during proof search.
  -- #268: a missing gauge-curve namespace poisoned the goal before the
  -- final `simpa` conversion; rewrite only the explicit coefficient identity.
  rw [actualOriginalCoreColorGaussCandidate_eq_combined_coordinates c f x]
  exact actualOriginalSmoothGaugeOrbit_combined_coordinate_derivative_zero c f x

#print axioms actualOriginalColorCoefficient_real_complex_sum_eq
#print axioms actualOriginalCoreColorGaussCandidate_eq_combined_coordinates
#print axioms actualOriginalSmoothGaugeOrbit_gaussCandidate_pointwise_derivative_zero
#check @actualOriginalSmoothGaugeOrbit_gaussCandidate_pointwise_derivative_zero
end
end FCP.BFSSSU2PhysicalDomainL6H5C3
