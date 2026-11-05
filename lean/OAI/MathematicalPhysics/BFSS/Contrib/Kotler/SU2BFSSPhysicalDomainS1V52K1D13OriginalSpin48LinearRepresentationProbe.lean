import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D12OriginalSpin48VectorActionLawsProbe

/-!
K1D13 — package the EXACT original Spin48 source-vector action
as a real-linear representation into GL(Source48Vector).

The source action is uniquely defined by original 48-real Clifford
generator conjugation in S1V31; it is not replaced by a different
SO action. All three declarations rely on qualified S1V31 additivity,
K1D12 real scalar-linearity / multiplication compatibility and
K1D11 original identity action. Inverse is source Spin-group inverse.

Not a quadratic isometry theorem, determinant theorem, SO48 lift,
surjectivity, covering, global Spin9 lift, or BFSS spectral theorem.
UNQUALIFIED until strict compiler, source, and axiom CI gate passes.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace FCP.BFSSS1V52K1D13
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- The original S1V31 action, packaged as a genuine real-linear map
by the previously qualified source additivity and scalar-linearity. -/
noncomputable def originalSourceSpin48LinearMap
    (s : spinGroup Q) : Source48Vector →ₗ[ℝ] Source48Vector where
  toFun := FCP.BFSSS1V31.sourceSpin48VectorAction s
  map_add' := FCP.BFSSS1V31.sourceSpin48VectorAction_add s
  map_smul' := FCP.BFSSS1V52K1D12.originalSourceSpin48VectorAction_smul s

/-- Every genuine source Spin48 action map is an invertible real-linear
map. The inverse is the SAME source action by the inverse Spin element. -/
noncomputable def originalSourceSpin48LinearEquiv
    (s : spinGroup Q) : Source48Vector ≃ₗ[ℝ] Source48Vector where
  toFun := FCP.BFSSS1V31.sourceSpin48VectorAction s
  invFun := FCP.BFSSS1V31.sourceSpin48VectorAction s⁻¹
  left_inv := by
    intro v
    rw [← FCP.BFSSS1V52K1D12.originalSourceSpin48VectorAction_mul (s⁻¹) s v]
    simpa only [inv_mul_cancel] using
      (FCP.BFSSS1V52K1D11.originalSourceSpin48_one_trivialAction v)
  right_inv := by
    intro v
    rw [← FCP.BFSSS1V52K1D12.originalSourceSpin48VectorAction_mul s (s⁻¹) v]
    simpa only [mul_inv_cancel] using
      (FCP.BFSSS1V52K1D11.originalSourceSpin48_one_trivialAction v)
  map_add' := FCP.BFSSS1V31.sourceSpin48VectorAction_add s
  map_smul' := FCP.BFSSS1V52K1D12.originalSourceSpin48VectorAction_smul s

/-- A genuine monoid/group homomorphism from the actual source
Spin48 group into invertible real-linear maps of the ORIGINAL 48-real
source vector space, not a claimed special orthogonal group hom. -/
noncomputable def originalSourceSpin48LinearRepresentation :
    spinGroup Q →* (Source48Vector ≃ₗ[ℝ] Source48Vector) where
  toFun := originalSourceSpin48LinearEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro v
    exact FCP.BFSSS1V52K1D11.originalSourceSpin48_one_trivialAction v
  map_mul' s t := by
    apply LinearEquiv.ext
    intro v
    exact FCP.BFSSS1V52K1D12.originalSourceSpin48VectorAction_mul s t v

#print axioms originalSourceSpin48LinearMap
#print axioms originalSourceSpin48LinearEquiv
#print axioms originalSourceSpin48LinearRepresentation

end
end FCP.BFSSS1V52K1D13
