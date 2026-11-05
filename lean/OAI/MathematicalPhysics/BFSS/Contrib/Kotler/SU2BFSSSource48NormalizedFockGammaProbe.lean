import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSSource48FockIndexBridgeProbe
import Mathlib.Tactic

/-!
# Exact Source48 basis labels: normalized Fock Majorana Clifford relations

The accepted BFSS Fock construction uses delta-one Majorana CAR.  By
contrast, the unit axes of the original positive Source48 quadratic form
have Clifford square one.  The required normalization is sqrt(2), not 1.

This module uses the accepted original source-label-to-Fock-index bridge
and the genuine original Fermion 2 Hilbert space. It proves only the
normalized generator's square and pairwise Clifford CAR on original
Source48 labels; a linear map for all source vectors, CliffordAlgHom,
Spin48 gauge lift, and physical BFSS spectral existence remain separate.

The normalization and proof structure are adapted from the FCP L9E2/E3
original-source research program, without importing the unrelated native
sixteen-block gauge ancestry of those source files.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSSource48NormalizedFockGamma
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSFermionF2
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSPairedThetaLabelCrosswalk
open FCP.BFSSSource48FockIndexBridge

private abbrev Op := Fermion 2 →L[ℂ] Fermion 2

/-- Exact positive-unit original Source48 Clifford-axis candidate. -/
noncomputable def sourceNormalizedGamma (p : Source48Label) : Op :=
  (↑(Real.sqrt 2) : ℂ) • majoranaCandidate p

/-- The original block/color axis selects the correspondingly normalized
G1A pairedTheta operator, using a separately proven source-label equality. -/
theorem sourceNormalizedGamma_eq_paired
    (j : Fin 8) (s : Fin 2) (A : ColorIndex 2) :
    sourceNormalizedGamma (sourceBlockColorLabel (j, s) A) =
      (↑(Real.sqrt 2) : ℂ) •
        pairedTheta (spinPairEquiv.symm (j, s)) A := by
  change (↑(Real.sqrt 2) : ℂ) •
      majoranaCandidate (sourceBlockColorLabel (j, s) A) =
    (↑(Real.sqrt 2) : ℂ) •
      pairedTheta (spinPairEquiv.symm (j, s)) A
  rw [sourceBlockColorMajorana_eq_G1APairedTheta]

/-- Source48 unit Clifford axes must square to the identity. -/
theorem sourceNormalizedGamma_sq_one (p : Source48Label) :
    sourceNormalizedGamma p * sourceNormalizedGamma p = (1 : Op) := by
  let t : Op := majoranaCandidate p
  have hcar : t * t + t * t = (1 : Op) := by
    dsimp [t]
    simpa using (FCP.BFSSFermionF2B2Indexed.majoranaCandidate_car p p)
  have hdouble : (2 : ℂ) • (t * t) = (1 : Op) :=
    (two_smul ℂ (t * t)).trans hcar
  have hsqrt : ((↑(Real.sqrt 2) : ℂ) *
      (↑(Real.sqrt 2) : ℂ)) = (2 : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  change ((↑(Real.sqrt 2) : ℂ) • t) *
    ((↑(Real.sqrt 2) : ℂ) • t) = 1
  rw [smul_mul_smul, hsqrt]
  exact hdouble

/-- Every pair of normalized source axes obeys the original
positive-unit Clifford CAR, with factor two on equal axes. -/
theorem sourceNormalizedGamma_pairwise_CAR (p q : Source48Label) :
    sourceNormalizedGamma p * sourceNormalizedGamma q +
      sourceNormalizedGamma q * sourceNormalizedGamma p =
      (if p = q then (2 : ℂ) else 0) • (1 : Op) := by
  let x : Op := majoranaCandidate p
  let y : Op := majoranaCandidate q
  have hcar : x * y + y * x =
      (if p = q then (1 : ℂ) else 0) • (1 : Op) := by
    exact FCP.BFSSFermionF2B2Indexed.majoranaCandidate_car p q
  have hsqrt : ((↑(Real.sqrt 2) : ℂ) *
      (↑(Real.sqrt 2) : ℂ)) = (2 : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  let c : ℂ := ↑(Real.sqrt 2)
  have hc2 : c * c = (2 : ℂ) := hsqrt
  change (c • x) * (c • y) + (c • y) * (c • x) =
    (if p = q then (2 : ℂ) else 0) • (1 : Op)
  calc
    (c • x) * (c • y) + (c • y) * (c • x) =
        (c * c) • (x * y + y * x) := by
      calc
        (c • x) * (c • y) + (c • y) * (c • x) =
          (c * c) • (x * y) + (c * c) • (y * x) := by
            rw [smul_mul_smul, smul_mul_smul]
        _ = (c * c) • (x * y + y * x) :=
          (smul_add (c * c) (x * y) (y * x)).symm
    _ = (2 : ℂ) • (x * y + y * x) := by rw [hc2]
    _ = (2 : ℂ) • ((if p = q then (1 : ℂ) else 0) • (1 : Op)) := by
      rw [hcar]
    _ = (if p = q then (2 : ℂ) else 0) • (1 : Op) := by
      by_cases hpq : p = q <;> simp [hpq, smul_smul]

#print axioms sourceNormalizedGamma_eq_paired
#print axioms sourceNormalizedGamma_sq_one
#print axioms sourceNormalizedGamma_pairwise_CAR

end
end FCP.BFSSSource48NormalizedFockGamma
