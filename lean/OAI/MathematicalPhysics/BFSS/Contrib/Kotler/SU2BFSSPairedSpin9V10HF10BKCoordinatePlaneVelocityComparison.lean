import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BJSourceCurveDerivatives
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BBOriginalGammaCanonicalSkewLieHom

/-!
F10BK — exact native coordinate-plane comparison between F10BB and
the original-gamma velocity of the actual source Spin9 curve.

Candidate only until strict compilation and independent type/axiom audit.
The input is the original native F_rs = E_rs - E_sr, packaged in exactly
Mathlib's so SpaceIndex ℝ. No extra half factor is placed in the input.
The output is the original gamma16 carrier.

This is a comparison of vector-space curve velocities on distinct source
coordinate planes. It does not identify a manifold tangent space, prove
a source group action differentiates to the native skew plane, or identify
the global F10BC manifold differential with F10BB. No atlas, Lie group,
covering/lift, Fock, gauge or spectral consequence is asserted.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9Plane
open scoped Matrix.Norms.Elementwise

/-- The unchanged source-native coordinate plane in the exact canonical Mathlib so(9) carrier. -/
noncomputable def source9CoordinatePlaneInSo (r s : SpaceIndex) :
    LieAlgebra.Orthogonal.so SpaceIndex ℝ :=
  ⟨coordinatePlane9 r s, by
    rw [LieAlgebra.Orthogonal.mem_so]
    exact coordinatePlane9_transpose r s⟩

/-- Exact positive half-gamma-product evaluation of the accepted canonical LieHom on F_rs. -/
theorem coordinateToOriginalGammaSkewLieHom_coordinatePlane_apply
    (r s : SpaceIndex) (hrs : r ≠ s) :
    ((coordinateToOriginalGammaSkewLieHom (source9CoordinatePlaneInSo r s)) : GammaMatrix) =
      (1 / 2 : ℝ) • (gamma r * gamma s) := by
  change coordinateToOriginalGammaLinearMap (coordinatePlane9 r s) = _
  rw [coordinateToOriginalGammaLinearMap_coordinatePlane, dite_eq_right hrs]

/-- Evaluating the actual Clifford curve velocity gives the canonical LieHom's native-plane image. -/
theorem source9PlaneCliffordVelocity_gamma_eq_coordinatePlaneLieHom
    (r s : SpaceIndex) (hrs : r ≠ s) :
    source9GammaCliffordAlgHom
      ((1 / 2 : ℝ) •
        (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s))) =
      ((coordinateToOriginalGammaSkewLieHom (source9CoordinatePlaneInSo r s)) : GammaMatrix) := by
  have hr : gammaNineRealLinear (source9CoordinateVector r) = gamma r := by
    simp [gammaNineRealLinear, source9CoordinateVector, Pi.single_apply]
  have hs : gammaNineRealLinear (source9CoordinateVector s) = gamma s := by
    simp [gammaNineRealLinear, source9CoordinateVector, Pi.single_apply]
  rw [coordinateToOriginalGammaSkewLieHom_coordinatePlane_apply r s hrs,
    map_smul, map_mul, source9GammaCliffordAlgHom_generator,
    source9GammaCliffordAlgHom_generator, hr, hs]

/-- The actual original-gamma image curve has velocity equal to F10BB evaluated on native F_rs. -/
theorem source9PlaneSpinCurve_gamma_hasDerivAt_coordinatePlaneLieHom
    (r s : SpaceIndex) (hrs : r ≠ s) :
    HasDerivAt (fun t : ℝ =>
      ((source9SpinGammaSpecialOrthogonalHom (source9PlaneSpinCurve r s hrs t)) : GammaMatrix))
      ((coordinateToOriginalGammaSkewLieHom (source9CoordinatePlaneInSo r s)) : GammaMatrix) 0 := by
  rw [coordinateToOriginalGammaSkewLieHom_coordinatePlane_apply r s hrs]
  exact source9PlaneSpinCurve_gamma_hasDerivAt_zero r s hrs

#print axioms source9CoordinatePlaneInSo
#print axioms coordinateToOriginalGammaSkewLieHom_coordinatePlane_apply
#print axioms source9PlaneCliffordVelocity_gamma_eq_coordinatePlaneLieHom
#print axioms source9PlaneSpinCurve_gamma_hasDerivAt_coordinatePlaneLieHom

end
end FCP.BFSSPairedSpin9Clifford
