import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7HSourceFiniteTimeThetaIntertwiningProbe

/-!
L6G7I — recover the exact forward theta covariance law for the
SOURCE exponential flow from the qualified L6G7H finite-time
conjugation identity. This is the algebraic comparison interface
required by the independently qualified G4H source gauge action.

Every operator is the literal pinned original bounded Fermion 2
Majorana, source fermionic color generator, and native +i SU(2)
adjoint coefficient. No equality to the G4B action is assumed here.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace FCP.BFSSSU2PhysicalDomainL6G7I
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2PhysicalDomainL6G6K
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G6Z
open FCP.BFSSSU2PhysicalDomainL6G7D
open FCP.BFSSSU2PhysicalDomainL6G7F
open FCP.BFSSSU2PhysicalDomainL6G7H

/-- Finite-time conjugation plus an exact left inverse gives
forward intertwining, in any monoid (no Fock elaboration). -/
private theorem abstract_conjugate_forward
    {R : Type*} [Monoid R]
    (V W T B : R) (hWV : W * V = 1)
    (hB : B = V * T * W) :
    V * T = B * V := by
  rw [hB]
  simp only [mul_assoc, hWV, mul_one]

attribute [local irreducible] pairedAlgebraData sourceFiberFermionColorGenerator

/-- Source flow transports a literal original theta forward into
the already-qualified color-rotated bounded source theta. -/
theorem sourceFlow_theta_forward_operator
    (c : ColorIndex 2) (spin : SpinIndex)
    (A : ColorIndex 2) (t : ℝ) :
    sourceFermionColorFlow c t *
      pairedAlgebraData.theta spin A =
    sourceRotatedTheta c spin A t *
      sourceFermionColorFlow c t := by
  exact abstract_conjugate_forward
    (sourceFermionColorFlow c t)
    (sourceFermionColorFlow c (-t))
    (pairedAlgebraData.theta spin A)
    (sourceRotatedTheta c spin A t)
    (sourceFermionColorFlow_neg_mul c t)
    (sourceRotatedTheta_eq_fermion_flow_conjugate c spin A t)

/-- EXACT full finite-time 48-Majorana forward operator covariance
with original SU(2) source-adjoint output-color coefficients.
This is the premise needed to compare with actual G4H gauge action,
NOT an assumption of implementer equality. -/
theorem sourceFlow_theta_forward_color_sum
    (c : ColorIndex 2) (spin : SpinIndex)
    (A : ColorIndex 2) (t : ℝ) :
    sourceFermionColorFlow c t *
      pairedAlgebraData.theta spin A =
    ∑ B : ColorIndex 2,
      (pairedAlgebraData.adjointCoefficient
        (sourcePlusIGaugeCurve c t) A B : ℂ) •
        (pairedAlgebraData.theta spin B *
          sourceFermionColorFlow c t) := by
  rw [sourceFlow_theta_forward_operator c spin A t]
  unfold sourceRotatedTheta
  simp only [Finset.sum_mul, smul_mul_assoc]

#print axioms abstract_conjugate_forward
#print axioms sourceFlow_theta_forward_operator
#print axioms sourceFlow_theta_forward_color_sum
#check @sourceFlow_theta_forward_color_sum

end
end FCP.BFSSSU2PhysicalDomainL6G7I
