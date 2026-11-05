import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7IOriginalFlowThetaForwardCovarianceProbe

/-!
L6G7J — put the actual source exponential V_c(t) on the same
invertible complex-linear-equivalence interface as the original
G4B/G4H exterior gauge implementation.

Input: fully qualified L6G7F source operator inverse laws and
L6G7I native +i coefficient forward covariance on the actual
48 original Majoranas of Fermion 2.

This module constructs V as an invertible complex linear map and
proves the SAME exact theta covariance as G4H. It does NOT assert
V = G4B; that remains a separate scalar-commutant/vacuum theorem.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace FCP.BFSSSU2PhysicalDomainL6G7J
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2PhysicalDomainL6G6K
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G6Z
open FCP.BFSSSU2PhysicalDomainL6G7F
open FCP.BFSSSU2PhysicalDomainL6G7I

/-- The genuine original bounded skew-generator exponential,
expressed as an invertible COMPLEX-linear operator on the SAME
original Fermion 2 Hilbert type as G4B. -/
noncomputable def sourceFlowLinearEquiv
    (c : ColorIndex 2) (t : ℝ) : Fermion 2 ≃ₗ[ℂ] Fermion 2 where
  toFun := sourceFermionColorFlow c t
  invFun := sourceFermionColorFlow c (-t)
  left_inv := by
    intro v
    have h := congrArg (fun T : SourceFiberEnd => T v)
      (sourceFermionColorFlow_neg_mul c t)
    simpa only [_root_.mul_apply_eq_comp, one_apply_eq_self] using h
  right_inv := by
    intro v
    have h := congrArg (fun T : SourceFiberEnd => T v)
      (sourceFermionColorFlow_mul_neg c t)
    simpa only [_root_.mul_apply_eq_comp, one_apply_eq_self] using h
  map_add' := (sourceFermionColorFlow c t).map_add
  map_smul' := (sourceFermionColorFlow c t).map_smul

/-- The invertible interface evaluates to the exact native bounded
Fock exponential, with no unfolding of its matrix-element source. -/
theorem sourceFlowLinearEquiv_apply
    (c : ColorIndex 2) (t : ℝ) (v : Fermion 2) :
    sourceFlowLinearEquiv c t v = sourceFermionColorFlow c t v := rfl

/-- Evaluate the qualified CLM equality of source native forward
theta covariance on one literal Fock state without unfolding its
exterior-algebra construction. -/
theorem sourceFlow_theta_forward_vector
    (c : ColorIndex 2) (spin : SpinIndex)
    (A : ColorIndex 2) (t : ℝ) (v : Fermion 2) :
    sourceFermionColorFlow c t
      (pairedAlgebraData.theta spin A v) =
    ∑ B : ColorIndex 2,
      (pairedAlgebraData.adjointCoefficient
        (sourcePlusIGaugeCurve c t) A B : ℂ) •
        pairedAlgebraData.theta spin B
          (sourceFermionColorFlow c t v) := by
  have h := congrArg (fun T : SourceFiberEnd => T v)
    (sourceFlow_theta_forward_color_sum c spin A t)
  -- The summands are source bounded operators, not ordinary functions;
  -- transport the finite sum through the bounded evaluation map.
  have hsum (f : ColorIndex 2 → SourceFiberEnd) :
      (∑ B : ColorIndex 2, f B) v =
        ∑ B : ColorIndex 2, (f B) v := by
    exact map_sum (ContinuousLinearMap.apply ℂ (Fermion 2) v) f Finset.univ
  simpa only [hsum, _root_.mul_apply_eq_comp,
    _root_.smul_apply] using h

/-- No covariance premise is assumed: exact same 48 source
theta, exact source coefficients, genuine source SU(2) +i curve
and source Fock exponential, cast into S1B's invertible interface. -/
theorem sourceFlowLinearEquiv_theta_covariant
    (c : ColorIndex 2) (t : ℝ)
    (spin : SpinIndex) (A : ColorIndex 2) (v : Fermion 2) :
    sourceFlowLinearEquiv c t (pairedTheta spin A v) =
      ∑ B : ColorIndex 2,
        (pairedAlgebraData.adjointCoefficient
          (sourcePlusIGaugeCurve c t) A B : ℂ) •
          pairedTheta spin B (sourceFlowLinearEquiv c t v) := by
  -- Normalize the *application* of the equivalence, rather than
  -- unfolding the entire source Fock structure in the proposition.
  simpa only [sourceFlowLinearEquiv_apply, pairedAlgebraData_theta] using
    (sourceFlow_theta_forward_vector c spin A t v)

#print axioms sourceFlowLinearEquiv
#print axioms sourceFlowLinearEquiv_apply
#print axioms sourceFlow_theta_forward_vector
#print axioms sourceFlowLinearEquiv_theta_covariant
#check @sourceFlowLinearEquiv_theta_covariant

end
end FCP.BFSSSU2PhysicalDomainL6G7J
