import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7FOriginalColorFlowOperatorCalculusProbe
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NoncommRing

/-!
L6G7G — independent finite-time source intertwining integration, Part 1:
prove the derivative of V_c(-t) B_{s,A}(t) V_c(t) is identically zero.

Mathematical inputs only: accepted L6G7E original bounded Majorana
commutator ODE, L6G7F exact bounded source exponential derivative,
flow-generator commutation, and a real Banach-algebra product rule.

Isolate the noncommutative cancellation over a GENERIC normed algebra.
Do not unfold source Fock operators, increase recursion limits, assume
the constant conclusion, or identify the external G4B gauge action.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace FCP.BFSSSU2PhysicalDomainL6G7G
noncomputable section
open scoped Topology
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2PhysicalDomainL6G6K
open FCP.BFSSSU2PhysicalDomainL6G6Z
open FCP.BFSSSU2PhysicalDomainL6G7D
open FCP.BFSSSU2PhysicalDomainL6G7E
open FCP.BFSSSU2PhysicalDomainL6G7F

/-- Derivative of the actual bounded source exponential at negative
real time, including the true outer chain-rule sign. -/
theorem sourceFermionColorFlow_derivative_neg_time
    (c : ColorIndex 2) (t : ℝ) :
    HasDerivAt (fun u : ℝ => sourceFermionColorFlow c (-u))
      (-(sourceFermionColorFlow c (-t) *
        sourceFiberFermionColorGenerator pairedAlgebraData c)) t := by
  have h := (sourceFermionColorFlow_derivative_operator c (-t)).scomp_of_eq
    t (hasDerivAt_neg t) (show (-t) = (fun u : ℝ => -u) t from rfl)
  simpa only [Function.comp_def, neg_one_smul] using h

/-- Zero derivative for the conjugated operator curve in an ABSTRACT
real normed algebra; no SU(2), CAR or concrete Fermion instance is
elaborated here. This is the noncommutative cancellation interface. -/
private theorem abstract_conjugated_curve_deriv_zero
    {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    (J : R) (U B V : ℝ → R) (t : ℝ)
    (hU : HasDerivAt U (-(U t * J)) t)
    (hB : HasDerivAt B (J * B t - B t * J) t)
    (hV : HasDerivAt V (V t * J) t)
    (hcomm : Commute J (V t)) :
    HasDerivAt (fun u => U u * B u * V u) (0 : R) t := by
  have hprod := (hU.mul hB).mul hV
  have hcancel :
      ((-(U t * J) * B t + U t * (J * B t - B t * J)) * V t +
        (U t * B t) * (V t * J)) = (0 : R) := by
    calc
      _ = (U t * B t) * (V t * J) -
            (U t * B t) * (J * V t) := by noncomm_ring
      _ = 0 := by rw [hcomm.eq]; exact sub_self _
  -- #187: Pi.mul_apply closes the derivative VALUE but not the
  -- equality of the two functions (U * B * V) and its lambda notation.
  -- Certify the value and function equalities separately, with no
  -- additional normed-algebra or concrete source unfolding.
  have hvalue :
      ((-(U t * J) * B t + U t * (J * B t - B t * J)) * V t +
        (U * B) t * (V t * J)) = (0 : R) := by
    simpa only [Pi.mul_apply] using hcancel
  have hcurve :
      (U * B * V : ℝ → R) =
        (fun u : ℝ => U u * B u * V u) := by
    funext u
    simp only [Pi.mul_apply]
  rw [hvalue] at hprod
  rw [hcurve] at hprod
  exact hprod

-- Keep opaque exactly those large source entities that previously
-- triggered repeated recursion-depth errors in direct ring elaboration.
attribute [local irreducible] pairedAlgebraData sourceFiberFermionColorGenerator

/-- The original bounded source operator-valued quantity is conserved
at the derivative level for every time, without any new premise.
Integration to a constant function is the NEXT separate obligation. -/
theorem sourceConjugatedRotatedTheta_deriv_zero
    (c : ColorIndex 2) (spin : SpinIndex)
    (A : ColorIndex 2) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        sourceFermionColorFlow c (-u) *
          sourceRotatedTheta c spin A u *
          sourceFermionColorFlow c u)
      (0 : SourceFiberEnd) t := by
  exact abstract_conjugated_curve_deriv_zero
    (sourceFiberFermionColorGenerator pairedAlgebraData c)
    (fun u : ℝ => sourceFermionColorFlow c (-u))
    (fun u : ℝ => sourceRotatedTheta c spin A u)
    (fun u : ℝ => sourceFermionColorFlow c u)
    t
    (sourceFermionColorFlow_derivative_neg_time c t)
    (sourceRotatedTheta_deriv_comm_all c spin A t)
    (sourceFermionColorFlow_derivative_operator c t)
    (sourceFermionColorGenerator_commute_flow c t)

#print axioms sourceFermionColorFlow_derivative_neg_time
#print axioms abstract_conjugated_curve_deriv_zero
#print axioms sourceConjugatedRotatedTheta_deriv_zero
#check @sourceConjugatedRotatedTheta_deriv_zero

end
end FCP.BFSSSU2PhysicalDomainL6G7G
