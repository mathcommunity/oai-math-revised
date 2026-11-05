import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BRSourceVectorOrthogonalHom
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Matrix.Normed

/-!
F10BS — whole original-nine matrix velocity of the actual source plane curve.

Candidate only until strict compilation and independent topology/type/axiom
audit. Use the qualified vector-valued conjugation derivative on original
coordinate columns, then the existing Pi derivative criterion twice.
The matrix norm is the standard scoped elementwise norm, with product
topology checked independently in the audit.

The derivative is literally coordinatePlane9 r s. This is an ordinary
ambient matrix-space derivative, not a source manifold tangent
identification, determinant-one theorem or global F10BC differential.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSPairedSpin9Plane
open scoped Matrix.Norms.Elementwise

/-- Every literal matrix entry has the corresponding full native coordinate-plane velocity. -/
theorem source9PlaneSpinCurve_vectorMatrix_entry_hasDerivAt_zero
    (r s : SpaceIndex) (hrs : r ≠ s) (i j : SpaceIndex) :
    HasDerivAt (fun t : ℝ => source9SpinVectorMatrixHom
      (source9PlaneSpinCurve r s hrs t) i j) (coordinatePlane9 r s i j) 0 := by
  have hcol := source9PlaneSpinCurve_vectorConjugation_hasDerivAt_zero
    r s hrs (source9CoordinateVector j)
  have hi := (hasDerivAt_pi.1 hcol) i
  have heq :
      (fun t : ℝ => source9SpinVectorMatrixHom (source9PlaneSpinCurve r s hrs t) i j) =
      (fun t : ℝ => source9SpinVectorConjugation
        (source9PlaneSpinCurve r s hrs t) (source9CoordinateVector j) i) := by
    funext t
    rfl
  have hvelocity :
      ((coordinatePlane9 r s).mulVec (source9CoordinateVector j)) i =
        coordinatePlane9 r s i j := by
    change dotProduct ((coordinatePlane9 r s) i) (Pi.single j (1 : ℝ)) =
      coordinatePlane9 r s i j
    rw [dotProduct_single, mul_one]
  rw [← heq, hvelocity] at hi
  exact hi

/-- The whole actual O(9) image matrix curve has literal native F_rs velocity at zero. -/
theorem source9PlaneSpinCurve_vectorOrthogonalMatrix_hasDerivAt_zero
    (r s : SpaceIndex) (hrs : r ≠ s) :
    HasDerivAt (fun t : ℝ =>
      ((source9SpinVectorOrthogonalHom (source9PlaneSpinCurve r s hrs t)) :
        Matrix SpaceIndex SpaceIndex ℝ)) (coordinatePlane9 r s) 0 := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  change HasDerivAt (fun t : ℝ => source9SpinVectorMatrixHom
    (source9PlaneSpinCurve r s hrs t) i j) (coordinatePlane9 r s i j) 0
  exact source9PlaneSpinCurve_vectorMatrix_entry_hasDerivAt_zero r s hrs i j

#print axioms source9PlaneSpinCurve_vectorMatrix_entry_hasDerivAt_zero
#print axioms source9PlaneSpinCurve_vectorOrthogonalMatrix_hasDerivAt_zero

end
end FCP.BFSSPairedSpin9Clifford
