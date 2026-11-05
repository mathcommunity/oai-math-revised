import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7GConjugatedThetaConstantDerivativeProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7BOriginalPlusIGaugeCurveGroupLawProbe
import Mathlib.Analysis.Calculus.MeanValue

/-!
L6G7H — integrate the accepted ORIGINAL bounded 48-Majorana source
commutator ODE into an exact all-time source fermion flow identity.

We use L6G7G's kernel-qualified zero derivative of
V_c(-t) B_{s,A}(t) V_c(t), Mathlib constancy over the real line,
and the source EXACT initial color matrix. All objects are original
pairedAlgebraData and its bounded source fermion generator.

Boundaries: V_c(t) is the bounded source fermionic exponential;
this is NOT YET its identification with the original externally
defined G4B gauge implementer, the physical Gauss constraint,
or any BFSS Hamiltonian spectral theorem.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace FCP.BFSSSU2PhysicalDomainL6G7H
noncomputable section

open scoped BigOperators Topology
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2PhysicalDomainL6G6K
open FCP.BFSSSU2PhysicalDomainL6G6Z
open FCP.BFSSSU2PhysicalDomainL6G7B
open FCP.BFSSSU2PhysicalDomainL6G7D
open FCP.BFSSSU2PhysicalDomainL6G7F
open FCP.BFSSSU2PhysicalDomainL6G7G

attribute [local irreducible] pairedAlgebraData sourceFiberFermionColorGenerator

/-- The color-rotated ORIGINAL theta starts from the source theta,
not a proxy basis or arbitrary equality premise. -/
theorem sourceRotatedTheta_zero (c : ColorIndex 2)
    (spin : SpinIndex) (A : ColorIndex 2) :
    sourceRotatedTheta c spin A 0 = pairedAlgebraData.theta spin A := by
  classical
  -- #190 reduced the source initial condition correctly to the finite
  -- Kronecker sum. Give the single surviving color term explicitly;
  -- do not unfold the original source Fock operators.
  simp only [sourceRotatedTheta, sourceNativeAdjointCoefficient_zero]
  rw [Fintype.sum_eq_single A]
  · simp
  · intro B hBA
    -- #191 reduced this branch to 0 • theta_B = 0 but the broad
    -- simp left that concrete operator-valued zero-smul unsolved.
    -- Use its module law directly after discharging the Kronecker test.
    simp only [if_neg (Ne.symm hBA), Complex.ofReal_zero]
    exact zero_smul ℂ (pairedAlgebraData.theta spin B)

/-- Exact initial value of the source-conjugated Majorana combination. -/
theorem sourceConjugatedRotatedTheta_zero (c : ColorIndex 2)
    (spin : SpinIndex) (A : ColorIndex 2) :
    sourceFermionColorFlow c (-(0 : ℝ)) *
        sourceRotatedTheta c spin A 0 *
        sourceFermionColorFlow c 0 =
      pairedAlgebraData.theta spin A := by
  simp only [neg_zero, sourceFermionColorFlow_zero,
    one_mul, mul_one, sourceRotatedTheta_zero]

/-- Actual original bounded theta source expression is constant
by the accepted operator-valued zero derivative on all of ℝ. -/
theorem sourceConjugatedRotatedTheta_constant
    (c : ColorIndex 2) (spin : SpinIndex)
    (A : ColorIndex 2) (t : ℝ) :
    sourceFermionColorFlow c (-t) *
      sourceRotatedTheta c spin A t *
      sourceFermionColorFlow c t =
        pairedAlgebraData.theta spin A := by
  let W : ℝ → SourceFiberEnd := fun u =>
    sourceFermionColorFlow c (-u) *
      sourceRotatedTheta c spin A u *
      sourceFermionColorFlow c u
  have hderiv (u : ℝ) : HasDerivAt W 0 u :=
    sourceConjugatedRotatedTheta_deriv_zero c spin A u
  have hdiffer : Differentiable ℝ W :=
    fun u => (hderiv u).differentiableAt
  have hzero (u : ℝ) : deriv W u = 0 := (hderiv u).deriv
  have hconst : W t = W 0 :=
    is_const_of_deriv_eq_zero hdiffer hzero t 0
  change
    sourceFermionColorFlow c (-t) *
      sourceRotatedTheta c spin A t *
      sourceFermionColorFlow c t =
    sourceFermionColorFlow c (-(0 : ℝ)) *
      sourceRotatedTheta c spin A 0 *
      sourceFermionColorFlow c 0 at hconst
  exact hconst.trans (sourceConjugatedRotatedTheta_zero c spin A)

/-- Cancellation in a generic ring with a right inverse; prevents
the original concrete Fock representation from being expanded. -/
private theorem abstract_source_conjugate_cancel
    {R : Type*} [Monoid R] (V W B : R)
    (h : V * W = 1) :
    V * (W * B * V) * W = B := by
  calc
    _ = (V * W) * B * (V * W) := by simp only [mul_assoc]
    _ = B := by simp only [h, one_mul, mul_one]

/-- FULL FINITE-TIME source bounded fermionic intertwining, in the
exact original source generator and 48 Majorana representation,
for every real time. No external gauge-implementation premise. -/
theorem sourceRotatedTheta_eq_fermion_flow_conjugate
    (c : ColorIndex 2) (spin : SpinIndex)
    (A : ColorIndex 2) (t : ℝ) :
    sourceRotatedTheta c spin A t =
      sourceFermionColorFlow c t *
        pairedAlgebraData.theta spin A *
        sourceFermionColorFlow c (-t) := by
  have hconst := sourceConjugatedRotatedTheta_constant c spin A t
  have hcancel := abstract_source_conjugate_cancel
    (sourceFermionColorFlow c t)
    (sourceFermionColorFlow c (-t))
    (sourceRotatedTheta c spin A t)
    (sourceFermionColorFlow_mul_neg c t)
  have hcongr := congrArg
    (fun T : SourceFiberEnd =>
      sourceFermionColorFlow c t * T *
        sourceFermionColorFlow c (-t)) hconst
  exact hcancel.symm.trans hcongr

#print axioms sourceRotatedTheta_zero
#print axioms sourceConjugatedRotatedTheta_zero
#print axioms sourceConjugatedRotatedTheta_constant
#print axioms sourceRotatedTheta_eq_fermion_flow_conjugate
#check @sourceRotatedTheta_eq_fermion_flow_conjugate

end
end FCP.BFSSSU2PhysicalDomainL6G7H
