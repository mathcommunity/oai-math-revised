import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5E1OriginalNormalizedFockMajoranaSelfAdjointProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52L9E5B0OriginalFockRealComplexOperatorScalarBridgeProbe

/-!
S1V52L9E5E2 — STAGED, UNQUALIFIED original all-real-source
Fock gamma self-adjointness.

The actual original real-linear Fock gamma (L9E4), its actual
real-to-complex scalar action (L9E5B0), and the original positive
sqrt2-normalized paired Majoranas (L9E5E1, strictly qualified)
are the ONLY ingredients. Prove finite self-adjoint complex-
weighted sums by Finset induction; do not rely on guessed
operator star or scalar-tower instances.

The original source Clifford star is NEGATIVE on odd generators.
This theorem concerns the original FOCK Hilbert adjoint, not
a global Clifford *-homomorphism, Spin implementer, or spectrum.
-/

set_option autoImplicit false
set_option maxHeartbeats 280000

namespace FCP.BFSSS1V52L9E5E2
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L9E2
open FCP.BFSSS1V52L9E4
open FCP.BFSSS1V52L9E5B0
open FCP.BFSSS1V52L9E5E1

private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- For EVERY real original 48-vector, the full original
Clifford-compatible normalized Fock gamma operator is
self-adjoint. No restriction to source coordinate axes. -/
theorem originalFockGammaRealLinear_selfAdjoint
    (v : Source48Vector) :
    IsSelfAdjoint (originalFockGammaRealLinear v) := by
  classical
  let γ (p : SourceLabel) : FockOp :=
    originalNormalizedFockMajorana
      (sourceBlockColorEquiv.symm p).1
      (sourceBlockColorEquiv.symm p).2
  have hterm (p : SourceLabel) :
      IsSelfAdjoint ((v p : ℂ) • γ p) := by
    have hc : IsSelfAdjoint (v p : ℂ) := by
      simp [isSelfAdjoint_iff]
    exact hc.smul
      (originalNormalizedFockMajorana_selfAdjoint
        (sourceBlockColorEquiv.symm p).1
        (sourceBlockColorEquiv.symm p).2)
  have hsum (s : Finset SourceLabel) :
      IsSelfAdjoint (s.sum (fun p => (v p : ℂ) • γ p)) := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        exact IsSelfAdjoint.zero FockOp
    | @insert p s hp ih =>
        rw [Finset.sum_insert hp]
        -- The Fock endomorphism star is DEFINITIONALLY its adjoint.
        -- Use pinned map_add of the actual conjugate-linear adjoint
        -- equivalence, not generic star_add (wrong inferred star).
        change ContinuousLinearMap.adjoint
          (((v p : ℂ) • γ p) +
            s.sum (fun q => (v q : ℂ) • γ q)) =
          ((v p : ℂ) • γ p) +
            s.sum (fun q => (v q : ℂ) • γ q)
        calc
          ContinuousLinearMap.adjoint
              (((v p : ℂ) • γ p) +
                s.sum (fun q => (v q : ℂ) • γ q)) =
            ContinuousLinearMap.adjoint ((v p : ℂ) • γ p) +
              ContinuousLinearMap.adjoint
                (s.sum (fun q => (v q : ℂ) • γ q)) := by
                  exact map_add
                    (ContinuousLinearMap.adjoint :
                      FockOp ≃ₗᵢ⋆[ℂ] FockOp)
                    ((v p : ℂ) • γ p)
                    (s.sum (fun q => (v q : ℂ) • γ q))
          _ = ((v p : ℂ) • γ p) +
                s.sum (fun q => (v q : ℂ) • γ q) := by
                  exact congrArg₂ (· + ·)
                    (hterm p).star_eq ih.star_eq
  have hrealToComplex :
      (∑ p : SourceLabel, (v p) • γ p) =
        (∑ p : SourceLabel, (v p : ℂ) • γ p) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact originalFockOperator_real_smul_eq_complex_smul (v p) (γ p)
  change IsSelfAdjoint
    (∑ p : SourceLabel, (v p) • γ p)
  rw [hrealToComplex]
  exact hsum Finset.univ

#print axioms originalFockGammaRealLinear_selfAdjoint

end
end FCP.BFSSS1V52L9E5E2
