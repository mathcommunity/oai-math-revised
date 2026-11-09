import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BLSourceCoordinateCommutatorAction
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BJSourceCurveDerivatives

/-!
F10BM — explicit actual source inverse curve and its vector-space derivative.

Candidate only until strict compilation and independent topology/type/axiom audit.
Use the existing source group inverse, which is Clifford star. Distinct
coordinate vectors anticommute under the actual quadratic polarization,
so the inverse curve has the exact half-angle expression with negative
bivector coefficient. Its PBW-space derivative is the negative of the
already qualified source curve velocity.

No normed-ring instance or multiplication bound is assumed or registered.
This is not yet the derivative of the conjugation action, a manifold
tangent theorem, or a global differential identification.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum

local instance : NormedAddCommGroup (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedAddCommGroup

local instance : NormedSpace ℝ (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedSpace

/-- Distinct actual source coordinate Clifford vectors anticommute, in the stated order. -/
theorem source9CoordinateClifford_anticommute
    (r s : SpaceIndex) (hrs : r ≠ s) :
    CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s) *
        CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) =
      -(CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
        CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s)) := by
  have hpolar : QuadraticMap.polar source9Quadratic
      (source9CoordinateVector s) (source9CoordinateVector r) = 0 := by
    rw [source9Quadratic_polar_coordinate]
    simp [source9CoordinateVector, Ne.symm hrs]
  simpa only [hpolar, map_zero, zero_sub] using
    (CliffordAlgebra.ι_mul_ι_comm (Q := source9Quadratic)
      (source9CoordinateVector s) (source9CoordinateVector r))

/-- Exact underlying Clifford expression of the actual source group inverse curve. -/
theorem source9PlaneSpinCurve_inv_coe
    (r s : SpaceIndex) (hrs : r ≠ s) (t : ℝ) :
    (((source9PlaneSpinCurve r s hrs t)⁻¹ : spinGroup source9Quadratic) :
      CliffordAlgebra source9Quadratic) =
      (Real.cos (t / 2)) • (1 : CliffordAlgebra source9Quadratic) +
        (Real.sin (t / 2)) •
          (-(CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
            CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s))) := by
  change star ((source9PlaneSpinCurve r s hrs t) : CliffordAlgebra source9Quadratic) = _
  rw [source9PlaneSpinCurve_coe]
  simp only [star_add, CliffordAlgebra.star_smul, star_one, star_mul,
    CliffordAlgebra.star_ι, neg_mul_neg, source9CoordinateClifford_anticommute r s hrs]

/-- The actual inverse source curve has negative source velocity at zero in the accepted PBW space. -/
theorem source9PlaneSpinCurve_inv_coe_hasDerivAt_zero
    (r s : SpaceIndex) (hrs : r ≠ s) :
    HasDerivAt (fun t : ℝ =>
      (((source9PlaneSpinCurve r s hrs t)⁻¹ : spinGroup source9Quadratic) :
        CliffordAlgebra source9Quadratic))
      (-((1 / 2 : ℝ) •
        (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s)))) 0 := by
  have heq :
      (fun t : ℝ =>
        (((source9PlaneSpinCurve r s hrs t)⁻¹ : spinGroup source9Quadratic) :
          CliffordAlgebra source9Quadratic)) =
      (fun t : ℝ => (Real.cos (t / 2)) • (1 : CliffordAlgebra source9Quadratic) +
        (Real.sin (t / 2)) •
          (-(CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
            CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s)))) := by
    funext t
    exact source9PlaneSpinCurve_inv_coe r s hrs t
  rw [heq]
  simpa only [smul_neg] using
    (realHalfAngleVectorCurve_hasDerivAt_zero
      (1 : CliffordAlgebra source9Quadratic)
      (-(CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
        CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s))))

#print axioms source9CoordinateClifford_anticommute
#print axioms source9PlaneSpinCurve_inv_coe
#print axioms source9PlaneSpinCurve_inv_coe_hasDerivAt_zero

end
end FCP.BFSSPairedSpin9Clifford
