import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V0StandaloneOrthogonalGeometryProbe
import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
K1D18U — source-exact nondegeneracy prerequisite for a future
original Spin(48) image/surjectivity investigation.

The source form is EXACTLY the pinned S1V0 weightedSumSquares
with weight one on Fin 24 × Fin 2. Mathlib's accepted radical
description gives zero radical without changing its basis, its
quadratic form, or the existing Clifford action.

This module does NOT prove any reflection-generation theorem,
SO48 surjectivity, Spin covering, global Spin9 covariance,
or BFSS spectral existence. It is a candidate until strict CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18U
noncomputable section
open FCP.BFSSS1V0

/-- Abstract finite-coordinate lemma, proved before specializing the
large source type: every coordinate weight is the nonzero scalar 1. -/
private theorem unitWeightedSumSquares_radical_eq_bot
    {ι : Type*} [Fintype ι] :
    (QuadraticMap.weightedSumSquares ℝ
      (fun _ : ι => (1 : ℝ))).radical =
        (⊥ : Submodule ℝ (ι → ℝ)) := by
  rw [QuadraticForm.radical_weightedSumSquares]
  simp [Pi.spanSubset]

/-- The radical of the EXACT original 48-label quadratic form is
zero, with no source replacement or coordinate reindexing. -/
theorem source48Quadratic_radical_eq_bot :
    source48Quadratic.radical =
      (⊥ : Submodule ℝ Source48Vector) := by
  exact unitWeightedSumSquares_radical_eq_bot (ι := Source48Label)

/-- Pinned Mathlib nondegeneracy of the SAME original source form,
derived from the zero radical over ℝ where 2 is invertible. -/
theorem source48Quadratic_nondegenerate :
    source48Quadratic.Nondegenerate := by
  exact (QuadraticMap.nondegenerate_iff_radical_eq_bot).2
    source48Quadratic_radical_eq_bot

#print axioms source48Quadratic_radical_eq_bot
#print axioms source48Quadratic_nondegenerate

end
end FCP.BFSSS1V52K1D18U
