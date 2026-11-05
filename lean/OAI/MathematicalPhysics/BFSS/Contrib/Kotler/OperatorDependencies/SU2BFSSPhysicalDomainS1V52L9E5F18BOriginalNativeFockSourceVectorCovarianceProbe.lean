import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F18AOriginalNativeFockPairedThetaRightCovarianceProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F15OriginalNativeSpin48FockLinearEquivGaugeHomProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG1APairedThetaProbe

/-!
L9E5F18B: exact original-source vector covariance candidate.
PROSPECTIVE AND UNQUALIFIED: never count this as accepted before the
actual preceding F18A source and this entire theorem have passed
source-pinned Lean + axiom audits.

Target precisely matches the explicit covariance premise of the accepted
S1H conditional source gauge-implementer uniqueness theorem. The native
Spin(48) gauge-to-Fock group hom is the genuine accepted F15 hom; the
fermionic operator on both sides is literal source pairedTheta. The
coefficient convention is original output-B/input-A, with no transpose.
The only scalar promotion is ℝ -> ℂ at the original Fermion-2 vector.

This does not itself identify an independent manuscript module, prove
physical-domain transport, or assert any spectral theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 360000

namespace FCP.BFSSS1V52L9E5F18B
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L8E
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5F14
open FCP.BFSSS1V52L9E5F15
open FCP.BFSSS1V52L9E5F18A
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG3A

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- Unconditional exact native SU(2) Fock representation covariance
for every original pairedTheta generator, with source complex scalars. -/
theorem originalNativeSixteenFock_source_vector_covariance
    (g : GaugeGroup 2) (α : SpinIndex) (A : ColorIndex 2)
    (v : Fermion 2) :
    originalNativeSixteenFockLinearEquivHom g (pairedTheta α A v) =
      ∑ B : ColorIndex 2,
        (pairedAlgebraData.adjointCoefficient g A B : ℂ) •
          pairedTheta α B (originalNativeSixteenFockLinearEquivHom g v) := by
  let U : FockOp :=
    originalFockCliffordAlgHom
      (((originalNativeSixteenSpinHom g : spinGroup Q) : C))
  have hright :=
    originalNativeSixteenFock_pairedTheta_right_covariance
      g (spinPairEquiv α) A
  have hrightv :
      U (pairedTheta α A v) =
        (∑ B : Fin 3, (adjointColorMatrix g B A) •
          (pairedTheta α B * U)) v := by
    simpa only [U, Equiv.symm_apply_apply,
      ContinuousLinearMap.mul_apply] using
      congrArg (fun T : FockOp => T v) hright
  have hsum :
      (∑ B : Fin 3, (adjointColorMatrix g B A) •
          (pairedTheta α B * U)) v =
      ∑ B : ColorIndex 2,
        (pairedAlgebraData.adjointCoefficient g A B : ℂ) •
          pairedTheta α B (U v) := by
    rw [ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro B _
    change (adjointColorMatrix g B A) •
      ((pairedTheta α B * U) v) =
        (↑(adjointColorMatrix g B A) : ℂ) •
          pairedTheta α B (U v)
    rw [ContinuousLinearMap.mul_apply]
    exact (Complex.coe_smul (adjointColorMatrix g B A)
      (pairedTheta α B (U v))).symm
  calc
    originalNativeSixteenFockLinearEquivHom g (pairedTheta α A v) =
        U (pairedTheta α A v) := rfl
    _ = (∑ B : Fin 3, (adjointColorMatrix g B A) •
          (pairedTheta α B * U)) v := hrightv
    _ = ∑ B : ColorIndex 2,
          (pairedAlgebraData.adjointCoefficient g A B : ℂ) •
            pairedTheta α B (U v) := hsum
    _ = _ := by rfl

#print axioms FCP.BFSSS1V52L9E5F18A.originalNativeSixteenFock_pairedTheta_right_covariance
#print axioms FCP.BFSSS1V52L9E5F15.originalNativeSixteenFockLinearEquivHom
#print axioms originalNativeSixteenFock_source_vector_covariance

end
end FCP.BFSSS1V52L9E5F18B
