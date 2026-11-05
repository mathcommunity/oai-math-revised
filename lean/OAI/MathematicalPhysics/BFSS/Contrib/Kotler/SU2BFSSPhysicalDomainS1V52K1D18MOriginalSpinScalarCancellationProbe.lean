import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18LOriginalLipschitzClosureGradeDetProbe

/-!
K1D18M — real source Spin(48) restriction of the accepted original
Lipschitz grade/determinant identity and Clifford unit cancellation.

Only actual Mathlib source spinGroup source48Quadratic, original source
Clifford units, and H determinant-unit character are used.

The conclusion of this module is scalar identity INSIDE the original
Clifford algebra, not yet scalar injectivity into ℝ, determinant +1,
SO48 group hom, covering, global Spin9, or BFSS spectral existence.
Candidate pending exact source and axiom strict qualification.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18M
noncomputable section

open FCP.BFSSS1V0
open CliffordAlgebra

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev L := lipschitzGroup Q
private abbrev chi := FCP.BFSSS1V52K1D18H.originalSourceLipschitzDeterminantCharacter

/-- Restrict the accepted genuine Lipschitz group embedding to the
actual original source Spin unit, not an independent new action. -/
private noncomputable def sourceSpinAsLipschitz (s : spinGroup Q) : L :=
  ⟨spinGroup.toUnits s,
    FCP.BFSSS1V52K1D18G.originalSourceSpin48_unit_mem_lipschitz s⟩

/-- The actual original source Spin unit has grade +1, and hence the
actual original Lipschitz determinant character scales it trivially.
This is a Clifford algebra identity on an actual unit. -/
theorem originalSourceSpin48_det_character_smul_unit (s : spinGroup Q) :
    (((chi (sourceSpinAsLipschitz s) : ℝˣ) : ℝ)) •
      (((spinGroup.toUnits s : Cˣ) : C)) =
        (((spinGroup.toUnits s : Cˣ) : C)) := by
  have hs : (((spinGroup.toUnits s : Cˣ) : C)) ∈ spinGroup Q := by
    change (s : C) ∈ spinGroup Q
    exact s.property
  calc
    _ = CliffordAlgebra.involute
      (((spinGroup.toUnits s : Cˣ) : C)) :=
        (FCP.BFSSS1V52K1D18L.originalSourceLipschitzGradeDetInvariant_all
          (sourceSpinAsLipschitz s)).symm
    _ = (((spinGroup.toUnits s : Cˣ) : C)) :=
      spinGroup.involute_eq hs

/-- Cancel the genuine original Clifford unit to obtain the scalar
identity in the ORIGINAL Clifford algebra. This is not yet a claimed
injectivity result for its scalar algebra map. -/
theorem originalSourceSpin48_det_character_smul_one (s : spinGroup Q) :
    (((chi (sourceSpinAsLipschitz s) : ℝˣ) : ℝ)) • (1 : C) =
      (1 : C) := by
  let u : Cˣ := spinGroup.toUnits s
  have hu :
      (((chi (sourceSpinAsLipschitz s) : ℝˣ) : ℝ)) • (u : C) =
        (u : C) :=
    originalSourceSpin48_det_character_smul_unit s
  calc
    (((chi (sourceSpinAsLipschitz s) : ℝˣ) : ℝ)) • (1 : C) =
        (((chi (sourceSpinAsLipschitz s) : ℝˣ) : ℝ)) •
          ((u : C) * ((u⁻¹ : Cˣ) : C)) := by simp
    _ = ((((chi (sourceSpinAsLipschitz s) : ℝˣ) : ℝ)) •
          (u : C)) * ((u⁻¹ : Cˣ) : C) := by rw [smul_mul_assoc]
    _ = (u : C) * ((u⁻¹ : Cˣ) : C) := by rw [hu]
    _ = 1 := by simp

#print axioms originalSourceSpin48_det_character_smul_unit
#print axioms originalSourceSpin48_det_character_smul_one

end
end FCP.BFSSS1V52K1D18M
