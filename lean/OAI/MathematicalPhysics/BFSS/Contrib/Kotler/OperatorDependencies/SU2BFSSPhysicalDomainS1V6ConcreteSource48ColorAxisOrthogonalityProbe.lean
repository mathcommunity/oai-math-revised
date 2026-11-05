import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V5ConcreteSixteenSourceColorBlocksProbe
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
S1V6 — candidate literal Q-unit / orthogonality for source 16x3 axes.

This attempts the FIRST genuine geometric ingredient for assembling
16 mutually orthogonal three-color planes inside the exact
Fin 24 × Fin 2 real source Majorana label space.

S1V5 chooses the explicit standard order from finProdFinEquiv. No
equality with the ORIGINAL colorModeEquiv / spinPairEquiv has yet
been established; the original-order bridge is a separate open
obligation. This file is NOT qualified until a pinned Lean job passes.
-/
set_option autoImplicit false
set_option maxHeartbeats 280000

namespace FCP.BFSSS1V6
noncomputable section

open Matrix
open FCP.BFSSS1V0
open FCP.BFSSS1V5

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

theorem source48Quadratic_eq_dot (v : Source48Vector) :
    Q v = dotProduct v v := by
  simp [source48Quadratic, QuadraticMap.weightedSumSquares_apply,
    dotProduct]

/-- Every concrete real source color-spin axis has exactly Q-norm
one, not a numerically approximated unit norm. -/
theorem sourceBlockColorAxis_unit
    (α : RealSpinBlock) (A : ColorLabel) :
    Q (sourceBlockColorAxis α A) = 1 := by
  rw [source48Quadratic_eq_dot]
  change (∑ i : SourceLabel,
      sourceBlockColorAxis α A i * sourceBlockColorAxis α A i) = 1
  calc
    (∑ i : SourceLabel,
      sourceBlockColorAxis α A i * sourceBlockColorAxis α A i) =
        ∑ i : SourceLabel,
          (if i = sourceBlockColorLabel α A then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases h : i = sourceBlockColorLabel α A
            · subst i
              simp [sourceBlockColorAxis]
            · simp [sourceBlockColorAxis, h]
    _ = 1 := by simp

/-- Different exact 48-Majorana coordinates have zero coordinatewise
product. No arbitrary orthogonality premise is inserted. -/
theorem sourceBlockColorAxis_mul_eq_zero
    (p q : RealSpinBlock × ColorLabel) (hpq : p ≠ q)
    (i : SourceLabel) :
    sourceBlockColorAxis p.1 p.2 i *
      sourceBlockColorAxis q.1 q.2 i = 0 := by
  by_cases h : i = sourceBlockColorLabel p.1 p.2
  · subst i
    rw [sourceBlockColorAxis_other q p hpq.symm]
    ring
  · have hz : sourceBlockColorAxis p.1 p.2 i = 0 := by
      simp [sourceBlockColorAxis, Pi.single_apply, h]
    rw [hz, zero_mul]

/-- Exact source-normalized Q-orthogonality of all distinct
16x3 coordinate axes, directly from the weighted quadratic form. -/
theorem sourceBlockColorAxis_ortho
    (p q : RealSpinBlock × ColorLabel) (hpq : p ≠ q) :
    Q.IsOrtho (sourceBlockColorAxis p.1 p.2)
      (sourceBlockColorAxis q.1 q.2) := by
  rw [QuadraticMap.isOrtho_def]
  simp only [source48Quadratic, QuadraticMap.weightedSumSquares_apply,
    one_smul, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hzero := sourceBlockColorAxis_mul_eq_zero p q hpq i
  nlinarith

#print axioms source48Quadratic_eq_dot
#print axioms sourceBlockColorAxis_unit
#print axioms sourceBlockColorAxis_mul_eq_zero
#print axioms sourceBlockColorAxis_ortho

end
end FCP.BFSSS1V6
