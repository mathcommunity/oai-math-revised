import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F16OriginalNativeFockNormalizedMajoranaColorCovarianceProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG1APairedThetaProbe

/-!
L9E5F17 — PROSPECTIVE ONLY, not accepted until a source-pinned strict
Lean gate proves the exact declaration and its imported F16 dependency.

The actual original Fermion 2 normalization is
  originalNormalizedFockMajorana α A =
    (Real.sqrt 2 : ℂ) • pairedTheta (spinPairEquiv.symm α) A.
The input/output color orientation is unchanged:
  adjointColorMatrix g B A = pairedAlgebraData.adjointCoefficient g A B.

This step removes the nonzero sqrt(2) factor from the *already accepted*
F16 normalized Majorana conjugation, without changing the source
fermionic gauge action, inserting a new representation, or claiming the
S1H relative-character uniqueness premise. Later gates must separately
move the right adjoint factor to the right, convert real to complex smul,
and transport from operators to vectors.

NOT a manuscript-module intertwiner, physical-domain equality, Spin(9)
spectral result, or BFSS mass gap.
-/

set_option autoImplicit false
set_option maxHeartbeats 360000

namespace FCP.BFSSS1V52L9E5F17
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L8E
open FCP.BFSSS1V52L9E2
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5F16
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG3A

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- Actual original unscaled pairedTheta covariance under conjugation
by the genuine sixteen-block native Spin(48) Fock operator. -/
theorem originalNativeSixteenFock_pairedTheta_conjugation
    (g : GaugeGroup 2) (α : RealSpinBlock) (A : Fin 3) :
    originalFockCliffordAlgHom
        (((originalNativeSixteenSpinHom g : spinGroup Q) : C)) *
      pairedTheta (spinPairEquiv.symm α) A *
      star (originalFockCliffordAlgHom
        (((originalNativeSixteenSpinHom g : spinGroup Q) : C))) =
      ∑ B : Fin 3, (adjointColorMatrix g B A) •
        pairedTheta (spinPairEquiv.symm α) B := by
  let U : FockOp :=
    originalFockCliffordAlgHom
      (((originalNativeSixteenSpinHom g : spinGroup Q) : C))
  let c : ℂ := (↑(Real.sqrt (2 : ℝ)) : ℂ)
  have hnormalized :
      U * (c • pairedTheta (spinPairEquiv.symm α) A) * star U =
        ∑ B : Fin 3, (adjointColorMatrix g B A) •
          (c • pairedTheta (spinPairEquiv.symm α) B) := by
    simpa only [U, c, originalNormalizedFockMajorana] using
      (originalNativeSixteenFock_normalizedMajorana_color_covariance g α A)
  have hleft :
      c • (U * pairedTheta (spinPairEquiv.symm α) A * star U) =
        U * (c • pairedTheta (spinPairEquiv.symm α) A) * star U := by
    rw [mul_smul_comm, smul_mul_assoc]
  have hright :
      (∑ B : Fin 3, (adjointColorMatrix g B A) •
        (c • pairedTheta (spinPairEquiv.symm α) B)) =
      c • (∑ B : Fin 3, (adjointColorMatrix g B A) •
        pairedTheta (spinPairEquiv.symm α) B) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro B _
    exact (smul_comm c (adjointColorMatrix g B A)
      (pairedTheta (spinPairEquiv.symm α) B)).symm
  have hscaled :
      c • (U * pairedTheta (spinPairEquiv.symm α) A * star U) =
      c • (∑ B : Fin 3, (adjointColorMatrix g B A) •
        pairedTheta (spinPairEquiv.symm α) B) := by
    calc
      _ = U * (c • pairedTheta (spinPairEquiv.symm α) A) * star U := hleft
      _ = ∑ B : Fin 3, (adjointColorMatrix g B A) •
          (c • pairedTheta (spinPairEquiv.symm α) B) := hnormalized
      _ = _ := hright
  have hc : c ≠ 0 := by
    change (↑(Real.sqrt (2 : ℝ)) : ℂ) ≠ 0
    exact_mod_cast (show Real.sqrt (2 : ℝ) ≠ 0 by positivity)
  have hcancel :
      U * pairedTheta (spinPairEquiv.symm α) A * star U =
        ∑ B : Fin 3, (adjointColorMatrix g B A) •
          pairedTheta (spinPairEquiv.symm α) B := by
    have h := congrArg (fun T : FockOp => c⁻¹ • T) hscaled
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h
  exact hcancel

-- Imported F16 is re-audited but must not be counted as a new F17 root.
#print axioms FCP.BFSSS1V52L9E5F16.originalNativeSixteenFock_normalizedMajorana_color_covariance
#print axioms originalNativeSixteenFock_pairedTheta_conjugation

end
end FCP.BFSSS1V52L9E5F17
