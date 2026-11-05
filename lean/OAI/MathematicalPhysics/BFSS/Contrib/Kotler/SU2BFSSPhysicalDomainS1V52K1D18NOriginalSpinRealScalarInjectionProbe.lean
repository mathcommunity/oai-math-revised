import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18MOriginalSpinScalarCancellationProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
K1D18N — source-exact REAL scalar-injectivity bridge for the
determinant-unit character of actual original Spin(48).

The original Clifford algebra is nontrivial over ℝ by the pinned
Clifford-to-exterior module equivalence (characteristic not 2).
Use the faithful ℝ-algebra scalar action on the *original* Clifford
algebra and the accepted M scalar-unit identity. No surrogate
Clifford algebra or Spin action is constructed.

K1D13 original linear representation equality, SO48 packaging,
kernel, covering, global Spin9, spectral existence remain separate.
Candidate pending strict source/axiom qualification.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18N
noncomputable section

open FCP.BFSSS1V0
open CliffordAlgebra

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev L := lipschitzGroup Q
private abbrev chi := FCP.BFSSS1V52K1D18H.originalSourceLipschitzDeterminantCharacter

private noncomputable def sourceSpinAsLipschitz (s : spinGroup Q) : L :=
  ⟨spinGroup.toUnits s,
    FCP.BFSSS1V52K1D18G.originalSourceSpin48_unit_mem_lipschitz s⟩

/-- The genuine H real determinant character equals +1 on each
actual original source Spin element. It follows from M's accepted
scalar action on Clifford 1, faithfulness of the ℝ-algebra action,
and pinned source Clifford nontriviality. -/
theorem originalSourceSpin48_lipschitzDetCharacter_real_one
    (s : spinGroup Q) :
    (((chi (sourceSpinAsLipschitz s) : ℝˣ) : ℝ)) = 1 := by
  have h : (((chi (sourceSpinAsLipschitz s) : ℝˣ) : ℝ)) • (1 : C) =
      (1 : C) := by
    exact FCP.BFSSS1V52K1D18M.originalSourceSpin48_det_character_smul_one s
  apply FaithfulSMul.algebraMap_injective ℝ C
  simpa only [Algebra.smul_def, mul_one, map_one] using h

#print axioms originalSourceSpin48_lipschitzDetCharacter_real_one

end
end FCP.BFSSS1V52K1D18N
