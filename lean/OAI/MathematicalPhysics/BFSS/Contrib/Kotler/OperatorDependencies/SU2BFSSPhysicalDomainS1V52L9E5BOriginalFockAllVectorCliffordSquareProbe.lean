import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52L9E5A2FiniteComplexWeightedFockCliffordSquareProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52L9E5B0OriginalFockRealComplexOperatorScalarBridgeProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E4OriginalFockRealLinearCliffordGeneratorMapProbe
import Mathlib.Basic.Complex.BigOperators

/-!
L9E5B — STAGED, UNQUALIFIED exact original BFSS all-vector
Clifford quadratic-square. The two explicitly visible prerequisites
are an independently checked abstract COMPLEX finite CAR contraction
(L9E5A2) and a separately checked REAL→COMPLEX scalar compatibility
lemma on the ACTUAL original Fock operator (L9E5B0).

No admitted scalar-tower instances or surrogate operator modules.
This file is NOT certified until both parents and its own exact
source specialization pass strict Lean/axiom validation.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52L9E5B
noncomputable section
open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L9E2
open FCP.BFSSS1V52L9E3
open FCP.BFSSS1V52L9E4
open FCP.BFSSS1V52L9E5A2
open FCP.BFSSS1V52L9E5B0

private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

theorem originalFockGammaRealLinear_sq (v : Source48Vector) :
    originalFockGammaRealLinear v *
      originalFockGammaRealLinear v =
        (source48Quadratic v) • (1 : FockOp) := by
  classical
  let γ (p : SourceLabel) : FockOp :=
    originalNormalizedFockMajorana
      (sourceBlockColorEquiv.symm p).1
      (sourceBlockColorEquiv.symm p).2
  let cc (p : SourceLabel) : ℂ := (v p : ℂ)
  have hdiag (p : SourceLabel) :
      γ p * γ p = (1 : FockOp) :=
    originalNormalizedFockMajorana_sq_one
      (sourceBlockColorEquiv.symm p).1
      (sourceBlockColorEquiv.symm p).2
  have hanti (p q : SourceLabel) (hpq : p ≠ q) :
      γ p * γ q + γ q * γ p = 0 := by
    have hnot :
        ¬ ((sourceBlockColorEquiv.symm p).1 =
              (sourceBlockColorEquiv.symm q).1 ∧
            (sourceBlockColorEquiv.symm p).2 =
              (sourceBlockColorEquiv.symm q).2) := by
      rintro ⟨ha, hb⟩
      exact hpq (sourceBlockColorEquiv.symm.injective (Prod.ext ha hb))
    change originalNormalizedFockMajorana
        (sourceBlockColorEquiv.symm p).1
        (sourceBlockColorEquiv.symm p).2 *
        originalNormalizedFockMajorana
          (sourceBlockColorEquiv.symm q).1
          (sourceBlockColorEquiv.symm q).2 +
      originalNormalizedFockMajorana
          (sourceBlockColorEquiv.symm q).1
          (sourceBlockColorEquiv.symm q).2 *
        originalNormalizedFockMajorana
          (sourceBlockColorEquiv.symm p).1
          (sourceBlockColorEquiv.symm p).2 = 0
    -- Gate #1: normalized original CAR gives zero COMPLEX-scalar
    -- multiplication on an actual original complex Fock operator.
    -- Discharge the operator zero separately with the typed lemma.
    calc
      _ = (0 : ℂ) • (1 : FockOp) := by
        simpa only [if_neg hnot] using
          (originalNormalizedFockMajorana_pairwise_CAR
            (sourceBlockColorEquiv.symm p).1
            (sourceBlockColorEquiv.symm q).1
            (sourceBlockColorEquiv.symm p).2
            (sourceBlockColorEquiv.symm q).2)
      _ = 0 := zero_smul ℂ (1 : FockOp)
  have hcomplex :
      (∑ p : SourceLabel, cc p • γ p) *
        (∑ p : SourceLabel, cc p • γ p) =
      (∑ p : SourceLabel, cc p * cc p) • (1 : FockOp) := by
    exact finiteComplexWeightedFockClifford_square
      (Finset.univ : Finset SourceLabel) cc γ hdiag hanti
  have hrealToComplex :
      (∑ p : SourceLabel, (v p) • γ p) =
        (∑ p : SourceLabel, cc p • γ p) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact originalFockOperator_real_smul_eq_complex_smul (v p) (γ p)
  have hcoeff :
      (∑ p : SourceLabel, cc p * cc p) =
        ((∑ p : SourceLabel, v p * v p : ℝ) : ℂ) := by
    calc
      (∑ p : SourceLabel, cc p * cc p) =
          ∑ p : SourceLabel, ((v p * v p : ℝ) : ℂ) := by
            apply Finset.sum_congr rfl
            intro p hp
            change (v p : ℂ) * (v p : ℂ) =
              ((v p * v p : ℝ) : ℂ)
            exact (Complex.ofReal_mul (v p) (v p)).symm
      _ = ((∑ p : SourceLabel, v p * v p : ℝ) : ℂ) :=
        (Complex.ofReal_sum (Finset.univ : Finset SourceLabel)
          (fun p => v p * v p)).symm
  calc
    originalFockGammaRealLinear v *
        originalFockGammaRealLinear v =
      (∑ p : SourceLabel, (v p) • γ p) *
        (∑ p : SourceLabel, (v p) • γ p) := by
          rfl
    _ = (∑ p : SourceLabel, cc p • γ p) *
          (∑ p : SourceLabel, cc p • γ p) := by
            rw [hrealToComplex]
    _ = (∑ p : SourceLabel, cc p * cc p) •
          (1 : FockOp) := hcomplex
    _ = (∑ p : SourceLabel, v p * v p) •
          (1 : FockOp) := by
            rw [hcoeff]
            exact
              (originalFockOperator_real_smul_eq_complex_smul
                (∑ p : SourceLabel, v p * v p) (1 : FockOp)).symm
    _ = (source48Quadratic v) • (1 : FockOp) := by
          rw [FCP.BFSSS1V6.source48Quadratic_eq_dot]
          rfl

#print axioms originalFockGammaRealLinear_sq
end
end FCP.BFSSS1V52L9E5B
