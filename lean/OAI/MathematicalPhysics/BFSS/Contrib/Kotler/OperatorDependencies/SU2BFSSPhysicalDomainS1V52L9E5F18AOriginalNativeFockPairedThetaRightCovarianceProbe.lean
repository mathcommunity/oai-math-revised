import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F17OriginalNativeFockUnscaledPairedThetaColorCovarianceProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F11OriginalNativeSixteenSpin48FockTwoSidedUnitarityProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52L9E5B0OriginalFockRealComplexOperatorScalarBridgeProbe

/-!
L9E5F18A — prospective, UNQUALIFIED until independently compiled.
No new assumptions, no source alteration, and no action on the original
gauge implementer are inferred.

From F17's true original unscaled Fermion-2 pairedTheta conjugation,
multiply on the RIGHT by the exact same source native Fock unitary and
use the independently accepted F11 Hilbert-adjoint LEFT inverse.

Operator order matters. The rightmost Fock unitary is not commuted
through a fermionic Majorana; only central real scalar coefficients
are carried through operator composition.

Still open: evaluation on Fermion vectors, exact ℝ-to-ℂ scalar
coefficient transport, S1H's full covariance hypothesis, comparison to
fermionGaugeLinearHom, and manuscript/physical/spectral transports.
-/

set_option autoImplicit false
set_option maxHeartbeats 360000

namespace FCP.BFSSS1V52L9E5F18A
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L8E
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5F11
open FCP.BFSSS1V52L9E5F17
open FCP.BFSSS1V52L9E5B0
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG3A

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- Exact original unscaled pairedTheta RIGHT covariance in the
original Fermion-2 complex continuous-linear operator algebra. -/
theorem originalNativeSixteenFock_pairedTheta_right_covariance
    (g : GaugeGroup 2) (α : RealSpinBlock) (A : Fin 3) :
    originalFockCliffordAlgHom
        (((originalNativeSixteenSpinHom g : spinGroup Q) : C)) *
      pairedTheta (spinPairEquiv.symm α) A =
      ∑ B : Fin 3, (adjointColorMatrix g B A) •
        (pairedTheta (spinPairEquiv.symm α) B *
          originalFockCliffordAlgHom
            (((originalNativeSixteenSpinHom g : spinGroup Q) : C))) := by
  let U : FockOp :=
    originalFockCliffordAlgHom
      (((originalNativeSixteenSpinHom g : spinGroup Q) : C))
  have hconj :
      U * pairedTheta (spinPairEquiv.symm α) A * star U =
        ∑ B : Fin 3, (adjointColorMatrix g B A) •
          pairedTheta (spinPairEquiv.symm α) B :=
    originalNativeSixteenFock_pairedTheta_conjugation g α A
  have hunit : star U * U = (1 : FockOp) :=
    originalNativeSixteenSpin48Fock_adjoint_mul g
  change
      U * pairedTheta (spinPairEquiv.symm α) A =
        ∑ B : Fin 3, (adjointColorMatrix g B A) •
          (pairedTheta (spinPairEquiv.symm α) B * U)
  calc
    U * pairedTheta (spinPairEquiv.symm α) A =
      (U * pairedTheta (spinPairEquiv.symm α) A) * (1 : FockOp) := by
        rw [mul_one]
    _ = (U * pairedTheta (spinPairEquiv.symm α) A) *
          (star U * U) := by rw [hunit]
    _ = (U * pairedTheta (spinPairEquiv.symm α) A * star U) * U := by
        simp only [mul_assoc]
    _ = (∑ B : Fin 3, (adjointColorMatrix g B A) •
          pairedTheta (spinPairEquiv.symm α) B) * U :=
        congrArg (fun T : FockOp => T * U) hconj
    _ = ∑ B : Fin 3, (adjointColorMatrix g B A) •
          (pairedTheta (spinPairEquiv.symm α) B * U) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro B _
        let r : ℝ := adjointColorMatrix g B A
        let T : FockOp := pairedTheta (spinPairEquiv.symm α) B
        change (r • T) * U = r • (T * U)
        calc
          (r • T) * U = ((r : ℂ) • T) * U := by
            rw [originalFockOperator_real_smul_eq_complex_smul]
          _ = (r : ℂ) • (T * U) := by rw [smul_mul_assoc]
          _ = r • (T * U) :=
            (originalFockOperator_real_smul_eq_complex_smul r (T * U)).symm

#print axioms FCP.BFSSS1V52L9E5F17.originalNativeSixteenFock_pairedTheta_conjugation
#print axioms FCP.BFSSS1V52L9E5F11.originalNativeSixteenSpin48Fock_adjoint_mul
#print axioms FCP.BFSSS1V52L9E5B0.originalFockOperator_real_smul_eq_complex_smul
#print axioms originalNativeSixteenFock_pairedTheta_right_covariance

end
end FCP.BFSSS1V52L9E5F18A
