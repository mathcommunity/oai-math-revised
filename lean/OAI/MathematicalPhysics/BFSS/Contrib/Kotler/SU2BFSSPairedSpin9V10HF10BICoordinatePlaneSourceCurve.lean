import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BHUnitVectorPairMembership
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Mul

/-!
F10BI — actual distinct-coordinate-plane source Spin9 curve and gamma image.

Candidate construction from accepted normalized-vector-pair membership.
The source basis, quadratic form, Clifford algebra and original gamma
representation are unchanged. The half-angle and product order are explicit.
The distinct-label hypothesis is necessary for this unit-vector formula;
the diagonal is not silently included.

This gate concerns algebraic curve values, value at zero and exact gamma
image only. It does not claim continuity, differentiability, one-parameter
homomorphism laws, a manifold, a tangent/skew identification or equality
of the global group-map differential with F10BB.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSGamma9

/-- The actual real source coordinate vector with its original nine-index label. -/
noncomputable def source9CoordinateVector (r : SpaceIndex) : SpaceIndex → ℝ :=
  Pi.single r 1

/-- Each actual source coordinate vector has quadratic norm one. -/
theorem source9CoordinateVector_unit (r : SpaceIndex) :
    source9Quadratic (source9CoordinateVector r) = 1 := by
  rw [source9Quadratic_eq_dot]
  simp [source9CoordinateVector]

/-- The explicit half-angle source vector for a distinct coordinate plane. -/
noncomputable def source9PlaneUnitVector (r s : SpaceIndex) (t : ℝ) : SpaceIndex → ℝ :=
  (Real.cos (t / 2)) • source9CoordinateVector r +
    (Real.sin (t / 2)) • source9CoordinateVector s

/-- Distinctness makes the actual half-angle source vector quadratically normalized. -/
theorem source9PlaneUnitVector_unit
    (r s : SpaceIndex) (hrs : r ≠ s) (t : ℝ) :
    source9Quadratic (source9PlaneUnitVector r s t) = 1 := by
  rw [source9Quadratic_eq_dot]
  simpa [source9PlaneUnitVector, source9CoordinateVector, hrs, Ne.symm hrs, smul_eq_mul, pow_two, add_comm]
    using (Real.sin_sq_add_cos_sq (t / 2))

/-- The normalized source vector pair, as an actual source Spin9 element for every parameter. -/
noncomputable def source9PlaneSpinCurve
    (r s : SpaceIndex) (hrs : r ≠ s) (t : ℝ) :
    spinGroup source9Quadratic :=
  source9UnitVectorPairSpin
    (source9CoordinateVector r) (source9PlaneUnitVector r s t)
    (source9CoordinateVector_unit r) (source9PlaneUnitVector_unit r s hrs t)

/-- Exact underlying Clifford rotor, with explicit product order and positive half-angle sign. -/
theorem source9PlaneSpinCurve_coe
    (r s : SpaceIndex) (hrs : r ≠ s) (t : ℝ) :
    ((source9PlaneSpinCurve r s hrs t) : CliffordAlgebra source9Quadratic) =
      (Real.cos (t / 2)) • (1 : CliffordAlgebra source9Quadratic) +
        (Real.sin (t / 2)) •
          (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
            CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s)) := by
  have hsq : CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
      CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) = 1 := by
    rw [CliffordAlgebra.ι_sq_scalar, source9CoordinateVector_unit, map_one]
  change CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
      CliffordAlgebra.ι source9Quadratic
        ((Real.cos (t / 2)) • source9CoordinateVector r +
          (Real.sin (t / 2)) • source9CoordinateVector s) = _
  rw [map_add, map_smul, map_smul, mul_add, mul_smul_comm, mul_smul_comm, hsq]

/-- The actual source curve passes through the actual group identity at parameter zero. -/
theorem source9PlaneSpinCurve_zero
    (r s : SpaceIndex) (hrs : r ≠ s) :
    source9PlaneSpinCurve r s hrs 0 = 1 := by
  apply Subtype.ext
  change ((source9PlaneSpinCurve r s hrs 0) : CliffordAlgebra source9Quadratic) = 1
  rw [source9PlaneSpinCurve_coe]
  simp

/-- Exact original 16-real gamma image of the actual source Spin9 curve. -/
theorem source9PlaneSpinCurve_gamma
    (r s : SpaceIndex) (hrs : r ≠ s) (t : ℝ) :
    ((source9SpinGammaSpecialOrthogonalHom (source9PlaneSpinCurve r s hrs t)) :
      GammaMatrix) =
      (Real.cos (t / 2)) • (1 : GammaMatrix) +
        (Real.sin (t / 2)) • (gamma r * gamma s) := by
  have hr : gammaNineRealLinear (source9CoordinateVector r) = gamma r := by
    simp [gammaNineRealLinear, source9CoordinateVector, Pi.single_apply]
  have hs : gammaNineRealLinear (source9CoordinateVector s) = gamma s := by
    simp [gammaNineRealLinear, source9CoordinateVector, Pi.single_apply]
  rw [source9SpinGammaSpecialOrthogonalHom_apply, source9PlaneSpinCurve_coe,
    map_add, map_smul, map_one, map_smul, map_mul,
    source9GammaCliffordAlgHom_generator, source9GammaCliffordAlgHom_generator, hr, hs]

#print axioms source9CoordinateVector
#print axioms source9CoordinateVector_unit
#print axioms source9PlaneUnitVector
#print axioms source9PlaneUnitVector_unit
#print axioms source9PlaneSpinCurve
#print axioms source9PlaneSpinCurve_coe
#print axioms source9PlaneSpinCurve_zero
#print axioms source9PlaneSpinCurve_gamma

end
end FCP.BFSSPairedSpin9Clifford
