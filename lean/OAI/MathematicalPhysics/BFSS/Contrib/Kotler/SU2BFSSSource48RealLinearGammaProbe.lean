import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSSource48NormalizedFockGammaProbe

/-!
# All original Source48 vectors: finite real-linear Fock gamma map

The accepted unit-axis CAR gives the correct normalized generator values,
but not yet an algebra representation.  This module constructs a finite
REAL-linear source map on the actual Source48Vector, then proves its exact
action on the original sourceBlockColorAxis and G1A pairedTheta indices.

The all-vector quadratic square law and a Clifford universal AlgHom are
separate research obligations.  Construction follows the finite linear
combination method of FCP L9E4, with the qualified source-index gamma.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSSource48RealLinearGamma
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSPairedThetaLabelCrosswalk
open FCP.BFSSSource48NormalizedFockGamma

private abbrev Op := Fermion 2 →L[ℂ] Fermion 2

/-- Finite real-linear extension of the ACTUAL Source48 unit generators. -/
noncomputable def sourceGammaRealLinear : Source48Vector →ₗ[ℝ] Op where
  toFun v := ∑ p : Source48Label, (v p) • sourceNormalizedGamma p
  map_add' := by
    intro v w
    change (∑ p : Source48Label,
      (v p + w p) • sourceNormalizedGamma p) =
        (∑ p : Source48Label, (v p) • sourceNormalizedGamma p) +
          ∑ p : Source48Label, (w p) • sourceNormalizedGamma p
    calc
      (∑ p : Source48Label, (v p + w p) • sourceNormalizedGamma p) =
          ∑ p : Source48Label,
            ((v p) • sourceNormalizedGamma p +
              (w p) • sourceNormalizedGamma p) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact add_smul (v p) (w p) (sourceNormalizedGamma p)
      _ = _ := Finset.sum_add_distrib
  map_smul' := by
    intro c v
    simp only [Pi.smul_apply, RingHom.id_apply,
      Finset.smul_sum, smul_smul, smul_eq_mul]

/-- Source48 real-coordinate unit axes map to their normalized
Fermion 2 Fock Majorana operators, with no reindexing ambiguity. -/
theorem sourceGammaRealLinear_axis
    (j : Fin 8) (s : Fin 2) (A : ColorIndex 2) :
    sourceGammaRealLinear (sourceBlockColorAxis (j, s) A) =
      sourceNormalizedGamma (sourceBlockColorLabel (j, s) A) := by
  classical
  change (∑ p : Source48Label,
      (sourceBlockColorAxis (j, s) A p) • sourceNormalizedGamma p) =
    sourceNormalizedGamma (sourceBlockColorLabel (j, s) A)
  rw [Finset.sum_eq_single (sourceBlockColorLabel (j, s) A)]
  · rw [sourceBlockColorAxis_self]
    exact one_smul ℝ (sourceNormalizedGamma (sourceBlockColorLabel (j, s) A))
  · intro p hp hne
    have hzero : sourceBlockColorAxis (j, s) A p = 0 := by
      have hne' : sourceBlockColorLabel (j, s) A ≠ p := Ne.symm hne
      simp [sourceBlockColorAxis, hne']
    rw [hzero]
    exact zero_smul ℝ (sourceNormalizedGamma p)
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

/-- The source-coordinate gamma map recovers the exact G1A
sqrt(2)-normalized pairedTheta family on every real source axis. -/
theorem sourceGammaRealLinear_axis_paired
    (j : Fin 8) (s : Fin 2) (A : ColorIndex 2) :
    sourceGammaRealLinear (sourceBlockColorAxis (j, s) A) =
      (↑(Real.sqrt 2) : ℂ) •
        pairedTheta (spinPairEquiv.symm (j, s)) A := by
  rw [sourceGammaRealLinear_axis, sourceNormalizedGamma_eq_paired]

#print axioms sourceGammaRealLinear_axis
#print axioms sourceGammaRealLinear_axis_paired

end
end FCP.BFSSSource48RealLinearGamma
