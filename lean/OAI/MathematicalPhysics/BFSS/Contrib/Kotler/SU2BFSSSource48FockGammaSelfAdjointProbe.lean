import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSSource48RealLinearGammaProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52L9E5B0OriginalFockRealComplexOperatorScalarBridgeProbe
import Mathlib.Algebra.Star.SelfAdjoint

/-!
# Original Source48 Fock gamma self-adjointness — bounded successor

RESEARCH CANDIDATE, not accepted before independent strict CI.

The precise source 48-index Majorana normalization and the real-linear
Source48Vector-to-original-Fermion-2 operator map are unchanged. This adapts
the FCP L9E5E1/E2 self-adjointness argument to the already source-identified
Source48 gammas, avoiding a second choice of source coordinate packing.

The CliffordAlgebra star is negative on odd generators, while the actual
Fock gamma is self-adjoint. Therefore these results do NOT claim that the
universal Clifford representation is a global star homomorphism.
Even-bivector star compatibility, Spin unitarity, gauge covariance, and
BFSS spectral existence remain separate obligations.

FCP E1 source blob 4360778128de2d353a665b80bf32eeb0dad25513;
FCP E2 source blob 6d689e8b067dbc0fd22f1b4160b7d6a3d82ce3f1.
-/ 

set_option autoImplicit false
set_option maxHeartbeats 320000

namespace FCP.BFSSSource48FockGammaSelfAdjoint
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSSource48NormalizedFockGamma
open FCP.BFSSSource48RealLinearGamma
open FCP.BFSSS1V52L9E5B0

private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- Every exactly sourced, sqrt(2)-normalized original Source48 Fock
Majorana generator is Hilbert self-adjoint. -/
theorem sourceNormalizedGamma_selfAdjoint (p : Source48Label) :
    IsSelfAdjoint (sourceNormalizedGamma p) := by
  change IsSelfAdjoint
    ((↑(Real.sqrt 2) : ℂ) • FCP.BFSSFermionF2.majoranaCandidate p)
  have hs : IsSelfAdjoint (↑(Real.sqrt 2) : ℂ) := by
    simp [isSelfAdjoint_iff]
  exact hs.smul (FCP.BFSSFermionF2.majoranaCandidate_selfAdjoint p)

/-- Every real original Source48 vector is sent to a self-adjoint
continuous complex-linear Fock operator, not merely every basis axis. -/
theorem sourceGammaRealLinear_selfAdjoint (v : Source48Vector) :
    IsSelfAdjoint (sourceGammaRealLinear v) := by
  classical
  let γ (p : Source48Label) : FockOp := sourceNormalizedGamma p
  have hterm (p : Source48Label) :
      IsSelfAdjoint ((v p : ℂ) • γ p) := by
    have hc : IsSelfAdjoint (v p : ℂ) := by
      simp [isSelfAdjoint_iff]
    exact hc.smul (sourceNormalizedGamma_selfAdjoint p)
  have hsum (s : Finset Source48Label) :
      IsSelfAdjoint (s.sum (fun p => (v p : ℂ) • γ p)) := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        exact IsSelfAdjoint.zero FockOp
    | @insert p s hp ih =>
        rw [Finset.sum_insert hp]
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
      (∑ p : Source48Label, (v p) • γ p) =
        ∑ p : Source48Label, (v p : ℂ) • γ p := by
    apply Finset.sum_congr rfl
    intro p hp
    exact originalFockOperator_real_smul_eq_complex_smul (v p) (γ p)
  change IsSelfAdjoint
    (∑ p : Source48Label, (v p) • γ p)
  rw [hrealToComplex]
  exact hsum Finset.univ

#print axioms sourceNormalizedGamma_selfAdjoint
#print axioms sourceGammaRealLinear_selfAdjoint

end
end FCP.BFSSSource48FockGammaSelfAdjoint

/-!
Independent contributor adaptation, 2026-10-27.
Original BFSS mathematical source remains attributed to the OpenAI authors.
Copyright (c) 2026 Evan T. Kotler.
SPDX-License-Identifier: Apache-2.0.
-/
