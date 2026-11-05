import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18NOriginalSpinRealScalarInjectionProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D13OriginalSpin48LinearRepresentationProbe

/-!
K1D18O — original-source action equality and determinant +1.

Rebase the qualified N real determinant character to the SAME
accepted K1D13 original source Spin48 real-linear equivalence.
No replacement Clifford action or quadratic isometry.
No SO48 hom yet; no kernel, covering, global Spin9, spectral claims.

Candidate pending strict independent source/axiom qualification.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18O
noncomputable section

open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev L := lipschitzGroup Q
private noncomputable def sourceSpinAsLipschitz (s : spinGroup Q) : L :=
  ⟨spinGroup.toUnits s,
    FCP.BFSSS1V52K1D18G.originalSourceSpin48_unit_mem_lipschitz s⟩

/-- The original S1V31/K1D13 Spin(48) action is EXACTLY the original
H Lipschitz action restricted via the accepted G inclusion. -/
theorem originalSourceSpin48_linearEquiv_eq_lipschitz
    (s : spinGroup Q) :
    FCP.BFSSS1V52K1D13.originalSourceSpin48LinearEquiv s =
    FCP.BFSSS1V52K1D18H.originalSourceLipschitzLinearEquiv
      (sourceSpinAsLipschitz s) := by
  apply LinearEquiv.ext
  intro v
  change FCP.BFSSS1V31.sourceSpin48VectorAction s v =
    FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction
      (spinGroup.toUnits s)
      (FCP.BFSSS1V52K1D18G.originalSourceSpin48_unit_mem_lipschitz s) v
  exact (FCP.BFSSS1V52K1D18G.sourceLipschitzVectorAction_agrees_originalSpin48 s v).symm

/-- The already accepted K1D13 source linear equivalence coerces
to the SAME original source linear map, not a fresh definition. -/
theorem originalSourceSpin48_linearEquiv_coe_eq_sourceLinearMap
    (s : spinGroup Q) :
    (FCP.BFSSS1V52K1D13.originalSourceSpin48LinearEquiv s :
        Source48Vector →ₗ[ℝ] Source48Vector) =
      FCP.BFSSS1V52K1D13.originalSourceSpin48LinearMap s := by
  rfl

/-- The exact accepted K1D13 ORIGINAL Spin(48) linear map has real
determinant +1, not merely a conditional two-generator theorem. -/
theorem originalSourceSpin48_originalLinearMap_det_one
    (s : spinGroup Q) :
    LinearMap.det (FCP.BFSSS1V52K1D13.originalSourceSpin48LinearMap s) = 1 := by
  have h := FCP.BFSSS1V52K1D18N.originalSourceSpin48_lipschitzDetCharacter_real_one s
  change ((LinearEquiv.det
      (FCP.BFSSS1V52K1D18H.originalSourceLipschitzLinearEquiv
        (sourceSpinAsLipschitz s)) : ℝˣ) : ℝ) = 1 at h
  rw [← originalSourceSpin48_linearEquiv_eq_lipschitz s,
    LinearEquiv.coe_det,
    originalSourceSpin48_linearEquiv_coe_eq_sourceLinearMap] at h
  exact h

#print axioms originalSourceSpin48_linearEquiv_eq_lipschitz
#print axioms originalSourceSpin48_linearEquiv_coe_eq_sourceLinearMap
#print axioms originalSourceSpin48_originalLinearMap_det_one

end
end FCP.BFSSS1V52K1D18O
