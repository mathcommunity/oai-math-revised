import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BTPBWBilinearMultiplicationSmoothness
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BOSourceVectorConjugationDerivative
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BGPBWSourceSpinTopologicalGroup
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
F10BU — jointly smooth ambient extension of actual source-vector conjugation.

Candidate only until fresh strict compilation and independent PBW/type/axiom
audit. Preserve the accepted PBW norm on the actual Clifford algebra and
the standard Pi norm on the original nine-vector space. Bundle the actual
linear reversal, vector embedding and accepted projection continuously.

The polynomial expression agrees with actual vector conjugation on Spin.
No source or target subgroup atlas, tangent identification or manifold
differential is constructed.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open scoped ContDiff

local instance f10buLocalNormedAddCommGroup : NormedAddCommGroup (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedAddCommGroup
local instance f10buLocalNormedSpace : NormedSpace ℝ (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedSpace
local instance f10buLocalFiniteDimensional : FiniteDimensional ℝ (CliffordAlgebra source9Quadratic) :=
  source9Clifford_finiteDimensional

/-- Actual Clifford grade reversal with the accepted PBW norm. -/
noncomputable def source9CliffordReverseCLM :
    CliffordAlgebra source9Quadratic →L[ℝ] CliffordAlgebra source9Quadratic :=
  { toLinearMap := CliffordAlgebra.reverse
    cont := source9Clifford_reverse_continuous_pbw }

/-- Actual embedding of the original nine-vector space into its Clifford algebra. -/
noncomputable def source9VectorEmbeddingCLM :
    (SpaceIndex → ℝ) →L[ℝ] CliffordAlgebra source9Quadratic :=
  { toLinearMap := CliffordAlgebra.ι source9Quadratic
    cont := (CliffordAlgebra.ι source9Quadratic).continuous_of_finiteDimensional }

/-- The already accepted canonical vector projection, continuously bundled. -/
noncomputable def source9VectorProjectionCLM :
    CliffordAlgebra source9Quadratic →L[ℝ] (SpaceIndex → ℝ) :=
  { toLinearMap := source9CliffordVectorProjection
    cont := source9CliffordVectorProjection_continuous_pbw }

/-- Ambient polynomial extending the actual Spin action; defined on every Clifford element. -/
noncomputable def source9AmbientVectorConjugation
    (a : CliffordAlgebra source9Quadratic) (z : SpaceIndex → ℝ) : SpaceIndex → ℝ :=
  source9CliffordVectorProjection
    (a * CliffordAlgebra.ι source9Quadratic z * CliffordAlgebra.reverse a)

/-- On the actual source group, ambient reversal is its inverse, so this is its exact action. -/
theorem source9AmbientVectorConjugation_eq_spin
    (g : spinGroup source9Quadratic) (z : SpaceIndex → ℝ) :
    source9AmbientVectorConjugation (g : CliffordAlgebra source9Quadratic) z =
      source9SpinVectorConjugation g z := by
  unfold source9AmbientVectorConjugation source9SpinVectorConjugation
  rw [source9Spin_inv_coe_eq_reverse]

/-- The ambient extension is jointly C^n in the Clifford element and vector for every order. -/
theorem source9AmbientVectorConjugation_contDiff_pbw (n : ℕ∞ω) :
    ContDiff ℝ n
      (fun az : CliffordAlgebra source9Quadratic × (SpaceIndex → ℝ) =>
        source9AmbientVectorConjugation az.1 az.2) := by
  have hi : ContDiff ℝ n
      (fun az : CliffordAlgebra source9Quadratic × (SpaceIndex → ℝ) =>
        CliffordAlgebra.ι source9Quadratic az.2) :=
    source9VectorEmbeddingCLM.contDiff.comp contDiff_snd
  have hr : ContDiff ℝ n
      (fun az : CliffordAlgebra source9Quadratic × (SpaceIndex → ℝ) =>
        CliffordAlgebra.reverse az.1) :=
    source9CliffordReverseCLM.contDiff.comp contDiff_fst
  have hleft : ContDiff ℝ n
      (fun az : CliffordAlgebra source9Quadratic × (SpaceIndex → ℝ) =>
        az.1 * CliffordAlgebra.ι source9Quadratic az.2) :=
    (source9Clifford_mul_contDiff_pbw n).comp₂ contDiff_fst hi
  have hproduct : ContDiff ℝ n
      (fun az : CliffordAlgebra source9Quadratic × (SpaceIndex → ℝ) =>
        az.1 * CliffordAlgebra.ι source9Quadratic az.2 * CliffordAlgebra.reverse az.1) :=
    (source9Clifford_mul_contDiff_pbw n).comp₂ hleft hr
  exact source9VectorProjectionCLM.contDiff.comp hproduct

#print axioms source9CliffordReverseCLM
#print axioms source9VectorEmbeddingCLM
#print axioms source9VectorProjectionCLM
#print axioms source9AmbientVectorConjugation
#print axioms source9AmbientVectorConjugation_eq_spin
#print axioms source9AmbientVectorConjugation_contDiff_pbw

end
end FCP.BFSSPairedSpin9Clifford
