import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5BOriginalDenseCoreGaussCandidateProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7POriginalSmoothCoreCoordinateGaugeGeneratorProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7QOriginalSourceGaugeTangentSignProbe

/-!
L6H5C1 — source-exact inverse bosonic gauge curve calculus on the
ORIGINAL BFSS SmoothCore 2 and literal source SU2 +i color subgroup.

Two independent finite-dimensional leaves are proved:
  (1) g_c(t)^(-1) = g_c(-t) IN the actual special unitary group,
  (2) the derivative of f(bosonGauge(g_c(t)^(-1), x)) at zero
      is MINUS the native +i forward bosonic coordinate sum, equivalently
      PLUS the original source gaugeTangent directional derivative.

This first leaf deliberately does NOT combine the Fock fiber action,
does NOT assert an all-time derivative or any strong FullL2 derivative,
and does NOT silently replace GaugeCore's original action.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5C1
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG2A
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7B
open FCP.BFSSSU2PhysicalDomainL6G7P
open FCP.BFSSSU2PhysicalDomainL6G7Q

/-- The exact source +i SU2 subgroup curve has inverse at -t,
inside the ORIGINAL genuine special unitary gauge group. -/
theorem sourcePlusIGaugeCurve_inv_eq_neg
    (c : ColorIndex 2) (t : ℝ) :
    (sourcePlusIGaugeCurve c t)⁻¹ =
      sourcePlusIGaugeCurve c (-t) := by
  have hmul :
      sourcePlusIGaugeCurve c t *
        sourcePlusIGaugeCurve c (-t) = 1 := by
    rw [← sourcePlusIGaugeCurve_add, add_neg_cancel,
      sourcePlusIGaugeCurve_one]
  calc
    (sourcePlusIGaugeCurve c t)⁻¹ =
        (sourcePlusIGaugeCurve c t)⁻¹ *
          (sourcePlusIGaugeCurve c t *
            sourcePlusIGaugeCurve c (-t)) := by
              rw [hmul, mul_one]
    _ = sourcePlusIGaugeCurve c (-t) := by
          rw [← mul_assoc, inv_mul_cancel, one_mul]

/-- Native source inverse bosonic pullback, differentiated at zero.
The original positive-i *forward* right-ordered coefficient sum
appears here with a MINUS sign, precisely because GaugeCore's
combined FullL2 action uses the INVERSE boson transform. -/
theorem originalSmoothCore_inverseBosonGauge_coordinate_derivative_zero
    (c : ColorIndex 2) (f : SmoothCore 2) (x : Boson 2) :
    HasDerivAt
      (fun t : ℝ =>
        f (bosonGauge ((sourcePlusIGaugeCurve c t)⁻¹) x))
      (-(∑ p : SpaceIndex × ColorIndex 2,
         (∑ A : ColorIndex 2,
           pairedAlgebraData.structureConstant p.2 A c * x (p.1,A)) •
             ((coordinateDerivative (N := 2) p.1 p.2 f) x)))
      0 := by
  have hforward :=
    actualBosonGauge_smoothCore_pullback_coordinate_derivative_zero c f x
  have hneg :=
    hforward.scomp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) (by simp)
  have hfun :
      (fun t : ℝ =>
        f (bosonGauge ((sourcePlusIGaugeCurve c t)⁻¹) x)) =
      ((fun t : ℝ =>
        f (bosonGauge (sourcePlusIGaugeCurve c t) x)) ∘
          (fun t : ℝ => -t)) := by
    funext t
    simp only [Function.comp_def, sourcePlusIGaugeCurve_inv_eq_neg]
  rw [hfun]
  simpa only [Function.comp_def, neg_zero, neg_one_smul] using hneg

/-- Reexpress the SAME inverse derivative using the pinned original
AlgebraData.gaugeTangent. The double sign reversal is physical,
not a Lean simplification convention. -/
theorem originalSmoothCore_inverseBosonGauge_originalTangent_derivative_zero
    (c : ColorIndex 2) (f : SmoothCore 2) (x : Boson 2) :
    HasDerivAt
      (fun t : ℝ =>
        f (bosonGauge ((sourcePlusIGaugeCurve c t)⁻¹) x))
      (fderiv ℝ (f : Boson 2 → Fermion 2) x
        (pairedAlgebraData.gaugeTangent x
          (EuclideanSpace.single c (1 : ℝ))))
      0 := by
  have hforward :=
    actualBosonGauge_smoothCore_pullback_neg_originalGaugeTangent c f x
  have hneg := hforward.scomp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) (by simp)
  have hfun :
      (fun t : ℝ =>
        f (bosonGauge ((sourcePlusIGaugeCurve c t)⁻¹) x)) =
      ((fun t : ℝ =>
        f (bosonGauge (sourcePlusIGaugeCurve c t) x)) ∘
          (fun t : ℝ => -t)) := by
    funext t
    simp only [Function.comp_def, sourcePlusIGaugeCurve_inv_eq_neg]
  rw [hfun]
  simpa only [Function.comp_def, neg_zero, neg_one_smul, neg_neg] using hneg

#print axioms sourcePlusIGaugeCurve_inv_eq_neg
#print axioms originalSmoothCore_inverseBosonGauge_coordinate_derivative_zero
#print axioms originalSmoothCore_inverseBosonGauge_originalTangent_derivative_zero
#check @originalSmoothCore_inverseBosonGauge_coordinate_derivative_zero

end
end FCP.BFSSSU2PhysicalDomainL6H5C1
