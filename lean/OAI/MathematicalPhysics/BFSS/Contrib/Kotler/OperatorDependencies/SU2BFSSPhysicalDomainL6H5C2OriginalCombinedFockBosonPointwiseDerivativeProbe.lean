import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5C1OriginalInverseBosonGaugeCurveDerivativeProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H0OriginalSmoothGaugeOrbitRepresentativeProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7FOriginalColorFlowOperatorCalculusProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7KOriginalSourceFlowExactGaugeImplementationProbe
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
L6H5C2 — SOURCE-EXACT pointwise derivative of the combined ORIGINAL
BFSS +i SU2 gauge orbit, using the actual exterior-Fock bounded flow
AND the inverse boson pullback together.

The pointwise original representative was separately qualified in H0
as the actual FullL2 source orbit almost everywhere. The Fock
operator derivative was independently source-qualified in G7F,
the equality to the genuine original G4B fiber action in G7K,
and the inverse boson source derivative with exact signs in H5C1.

The proof deliberately applies pinned Mathlib
HasDerivAt.clm_apply to the operator and moving state, rather than
elaborating the actual 48 Majorana Fock expression.

The derivative here is pointwise in Boson 2. This alone is NOT
the norm derivative in FullL2, generator closure, domain identification,
essential self-adjointness or a BFSS spectral theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 220000

namespace FCP.BFSSSU2PhysicalDomainL6H5C2
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG2A
open FCP.BFSSSU2GaugeG4B
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6G6K
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G6Z
open FCP.BFSSSU2PhysicalDomainL6G7F
open FCP.BFSSSU2PhysicalDomainL6G7K
open FCP.BFSSSU2PhysicalDomainL6H0
open FCP.BFSSSU2PhysicalDomainL6H5C1

/-- The true combined SU2 orbit representative differentiates
pointwise with its EXACT bounded Fock plus ORIGINAL inverse bosonic
gaugeTangent. No surrogate action or unproved differentiability. -/
theorem actualOriginalSmoothGaugeOrbit_combined_pointwise_derivative_zero
    (c : ColorIndex 2) (f : SmoothCore 2) (x : Boson 2) :
    HasDerivAt
      (fun t : ℝ =>
        actualOriginalSmoothGaugeOrbitRepresentative f
          (sourcePlusIGaugeCurve c t) x)
      (sourceFiberFermionColorGenerator pairedAlgebraData c (f x) +
        fderiv ℝ (f : Boson 2 → Fermion 2) x
          (pairedAlgebraData.gaugeTangent x
            (EuclideanSpace.single c (1 : ℝ))))
      0 := by
  have hoper :
      HasDerivAt (fun t : ℝ => sourceFermionColorFlow c t)
        (sourceFiberFermionColorGenerator pairedAlgebraData c) 0 := by
    simpa only [sourceFermionColorFlow_zero, one_mul] using
      sourceFermionColorFlow_derivative_operator c 0
  have hvec :=
    originalSmoothCore_inverseBosonGauge_originalTangent_derivative_zero
      c f x
  -- #266: the time parameter is real while the bounded Fock
  -- endomorphisms are complex-linear. Move the exact same operator
  -- through pinned continuous scalar restriction before using
  -- the real-parameter CLM evaluation product rule.
  let R : (Fermion 2 →L[ℂ] Fermion 2) →L[ℝ]
      (Fermion 2 →L[ℝ] Fermion 2) :=
    ContinuousLinearMap.restrictScalarsL ℂ (Fermion 2) (Fermion 2) ℝ ℝ
  have hoperR :
      HasDerivAt (fun t : ℝ => R (sourceFermionColorFlow c t))
        (R (sourceFiberFermionColorGenerator pairedAlgebraData c)) 0 := by
    simpa only [Function.comp_def] using
      (R.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hoper)
  have hprod := hoperR.clm_apply hvec
  change HasDerivAt
    (fun t : ℝ =>
      sourceFermionColorFlow c t
        (f (bosonGauge ((sourcePlusIGaugeCurve c t)⁻¹) x)))
    (sourceFiberFermionColorGenerator pairedAlgebraData c
      (f (bosonGauge ((sourcePlusIGaugeCurve c (0 : ℝ))⁻¹) x)) +
      sourceFermionColorFlow c 0
        (fderiv ℝ (f : Boson 2 → Fermion 2) x
          (pairedAlgebraData.gaugeTangent x
            (EuclideanSpace.single c (1 : ℝ)))))
    0 at hprod
  have hzero :
      f (bosonGauge ((sourcePlusIGaugeCurve c (0 : ℝ))⁻¹) x) =
        f x := by
    simp [sourcePlusIGaugeCurve_one]
  have hprod' :
      HasDerivAt
        (fun t : ℝ =>
          sourceFermionColorFlow c t
            (f (bosonGauge ((sourcePlusIGaugeCurve c t)⁻¹) x)))
        (sourceFiberFermionColorGenerator pairedAlgebraData c (f x) +
          fderiv ℝ (f : Boson 2 → Fermion 2) x
            (pairedAlgebraData.gaugeTangent x
              (EuclideanSpace.single c (1 : ℝ))))
        0 := by
    simpa only [hzero, sourceFermionColorFlow_zero, one_apply_eq_self]
      using hprod
  have hsource (t : ℝ) :
      actualOriginalSmoothGaugeOrbitRepresentative f
        (sourcePlusIGaugeCurve c t) x =
        sourceFermionColorFlow c t
          (f (bosonGauge ((sourcePlusIGaugeCurve c t)⁻¹) x)) := by
    change fermionGaugeLinearEquiv (sourcePlusIGaugeCurve c t)
      (f (bosonGauge ((sourcePlusIGaugeCurve c t)⁻¹) x)) =
      sourceFermionColorFlow c t
        (f (bosonGauge ((sourcePlusIGaugeCurve c t)⁻¹) x))
    exact (sourceFermionColorFlow_eq_actualGauge_apply c t _).symm
  convert hprod' using 1
  funext t
  exact hsource t

/-- The identical full original combined derivative with the native
+ i structureConstant and RIGHT-ORDERED source coordinateDerivative
sum. The minus sign is forced by the inverse bosonic pullback. -/
theorem actualOriginalSmoothGaugeOrbit_combined_coordinate_derivative_zero
    (c : ColorIndex 2) (f : SmoothCore 2) (x : Boson 2) :
    HasDerivAt
      (fun t : ℝ =>
        actualOriginalSmoothGaugeOrbitRepresentative f
          (sourcePlusIGaugeCurve c t) x)
      (sourceFiberFermionColorGenerator pairedAlgebraData c (f x) -
        ∑ p : SpaceIndex × ColorIndex 2,
          (∑ A : ColorIndex 2,
            pairedAlgebraData.structureConstant p.2 A c * x (p.1, A)) •
              ((coordinateDerivative (N := 2) p.1 p.2 f) x))
      0 := by
  have hEq :
      fderiv ℝ (f : Boson 2 → Fermion 2) x
        (pairedAlgebraData.gaugeTangent x
          (EuclideanSpace.single c (1 : ℝ))) =
      -(∑ p : SpaceIndex × ColorIndex 2,
        (∑ A : ColorIndex 2,
          pairedAlgebraData.structureConstant p.2 A c * x (p.1,A)) •
            ((coordinateDerivative (N := 2) p.1 p.2 f) x)) :=
    (originalSmoothCore_inverseBosonGauge_originalTangent_derivative_zero
      c f x).unique
      (originalSmoothCore_inverseBosonGauge_coordinate_derivative_zero
        c f x)
  rw [sub_eq_add_neg]
  simpa only [hEq] using
    actualOriginalSmoothGaugeOrbit_combined_pointwise_derivative_zero c f x

#print axioms actualOriginalSmoothGaugeOrbit_combined_pointwise_derivative_zero
#print axioms actualOriginalSmoothGaugeOrbit_combined_coordinate_derivative_zero
#check @actualOriginalSmoothGaugeOrbit_combined_pointwise_derivative_zero
#check @actualOriginalSmoothGaugeOrbit_combined_coordinate_derivative_zero

end
end FCP.BFSSSU2PhysicalDomainL6H5C2
