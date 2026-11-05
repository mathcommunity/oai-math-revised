import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18OOriginalSpinDeterminantOneProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D16OriginalSpin48QuadraticIsometryProbe

/-!
K1D18P — the previously accepted original source Spin48
QUADRATIC ISOMETRY has real determinant +1.

Uses exactly the qualified K1D16 original source quadratic isometry,
its accepted equality with the K1D13 original vector action,
and the accepted K1D18O unconditional original determinant-one theorem.

This is the same original 48 real labels and the same
source48Quadratic, with no new action, alternative metric, or Spin
factorization. Constructing a special-orthogonal group homomorphism,
kernel/covering, global Spin9 lift and BFSS spectral claims
remain separate strict proof obligations.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18P
noncomputable section

open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- The original quadratic isometry has EXACTLY the accepted
K1D13 original Spin48 real-linear map as its linear part. -/
theorem originalSourceSpin48_quadraticIsometry_linearMap_eq
    (s : spinGroup Q) :
    ((FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry s :
        Source48Vector ≃ₗ[ℝ] Source48Vector) :
      Source48Vector →ₗ[ℝ] Source48Vector) =
      FCP.BFSSS1V52K1D13.originalSourceSpin48LinearMap s := by
  rw [FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry_underlyingLinearEquiv,
    FCP.BFSSS1V52K1D18O.originalSourceSpin48_linearEquiv_coe_eq_sourceLinearMap]

/-- The ACTUAL accepted original 48-real Spin quadratic isometry
preserves orientation: its original real determinant is +1.
No new or surrogate geometric action is used. -/
theorem originalSourceSpin48_quadraticIsometry_det_one
    (s : spinGroup Q) :
    LinearMap.det
      ((FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry s :
          Source48Vector ≃ₗ[ℝ] Source48Vector) :
        Source48Vector →ₗ[ℝ] Source48Vector) = 1 := by
  rw [originalSourceSpin48_quadraticIsometry_linearMap_eq]
  exact FCP.BFSSS1V52K1D18O.originalSourceSpin48_originalLinearMap_det_one s

#print axioms originalSourceSpin48_quadraticIsometry_linearMap_eq
#print axioms originalSourceSpin48_quadraticIsometry_det_one

end
end FCP.BFSSS1V52K1D18P
