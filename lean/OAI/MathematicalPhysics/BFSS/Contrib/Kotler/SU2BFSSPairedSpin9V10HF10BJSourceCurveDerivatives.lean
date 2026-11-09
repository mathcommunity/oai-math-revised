import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BICoordinatePlaneSourceCurve
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BEPBWTopologyGammaContinuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Matrix.Normed

/-!
F10BJ — derivatives at zero of the actual distinct-plane source curve
and its exact original gamma matrix image.

Candidate only until fresh strict compilation and independent topology,
type and axiom checks pass. The Clifford-valued derivative uses exactly
the accepted named PBW normed structures. The gamma-valued derivative uses
the standard original 16-real matrix topology. Both are ordinary
real-parameter derivatives in vector spaces, obtained by explicit
equalities with the accepted half-angle formulas.

No manifold tangent space, source/target Lie-group atlas, global group-map
differential, F10BB source-plane normalization comparison, covering/lift,
Fock, gauge-domain or spectral conclusion is asserted.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSGamma9
open scoped Matrix.Norms.Elementwise

local instance : NormedAddCommGroup (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedAddCommGroup

local instance : NormedSpace ℝ (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedSpace

/-- The explicit half-angle vector curve has velocity one half of its sine coefficient at zero. -/
theorem realHalfAngleVectorCurve_hasDerivAt_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (a b : V) :
    HasDerivAt (fun t : ℝ => (Real.cos (t / 2)) • a + (Real.sin (t / 2)) • b)
      ((1 / 2 : ℝ) • b) 0 := by
  have hc : HasDerivAt (fun t : ℝ => Real.cos (t / 2)) 0 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).div_const 2).cos)
  have hs : HasDerivAt (fun t : ℝ => Real.sin (t / 2)) (1 / 2 : ℝ) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).div_const 2).sin)
  have hadd :
      ((fun t : ℝ => (Real.cos (t / 2)) • a) +
        (fun t : ℝ => (Real.sin (t / 2)) • b)) =
      (fun t : ℝ => (Real.cos (t / 2)) • a + (Real.sin (t / 2)) • b) := by
    funext t
    rfl
  have hsum := (hc.smul_const a).add (hs.smul_const b)
  rw [hadd] at hsum
  simpa only [zero_smul, zero_add] using hsum

/-- The exact source Spin9 curve, coerced to its PBW-normed Clifford space, has the stated velocity. -/
theorem source9PlaneSpinCurve_coe_hasDerivAt_zero
    (r s : SpaceIndex) (hrs : r ≠ s) :
    HasDerivAt (fun t : ℝ =>
      ((source9PlaneSpinCurve r s hrs t) : CliffordAlgebra source9Quadratic))
      ((1 / 2 : ℝ) •
        (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s))) 0 := by
  have heq :
      (fun t : ℝ => ((source9PlaneSpinCurve r s hrs t) : CliffordAlgebra source9Quadratic)) =
      (fun t : ℝ => (Real.cos (t / 2)) • (1 : CliffordAlgebra source9Quadratic) +
        (Real.sin (t / 2)) •
          (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
            CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s))) := by
    funext t
    exact source9PlaneSpinCurve_coe r s hrs t
  rw [heq]
  exact realHalfAngleVectorCurve_hasDerivAt_zero
    (1 : CliffordAlgebra source9Quadratic)
    (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
      CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s))

/-- The exact F10BC original-gamma image curve has positive half-gamma-product velocity at zero. -/
theorem source9PlaneSpinCurve_gamma_hasDerivAt_zero
    (r s : SpaceIndex) (hrs : r ≠ s) :
    HasDerivAt (fun t : ℝ =>
      ((source9SpinGammaSpecialOrthogonalHom (source9PlaneSpinCurve r s hrs t)) : GammaMatrix))
      ((1 / 2 : ℝ) • (gamma r * gamma s)) 0 := by
  have heq :
      (fun t : ℝ =>
        ((source9SpinGammaSpecialOrthogonalHom (source9PlaneSpinCurve r s hrs t)) : GammaMatrix)) =
      (fun t : ℝ => (Real.cos (t / 2)) • (1 : GammaMatrix) +
        (Real.sin (t / 2)) • (gamma r * gamma s)) := by
    funext t
    exact source9PlaneSpinCurve_gamma r s hrs t
  rw [heq]
  exact realHalfAngleVectorCurve_hasDerivAt_zero (1 : GammaMatrix) (gamma r * gamma s)

#print axioms realHalfAngleVectorCurve_hasDerivAt_zero
#print axioms source9PlaneSpinCurve_coe_hasDerivAt_zero
#print axioms source9PlaneSpinCurve_gamma_hasDerivAt_zero

end
end FCP.BFSSPairedSpin9Clifford
