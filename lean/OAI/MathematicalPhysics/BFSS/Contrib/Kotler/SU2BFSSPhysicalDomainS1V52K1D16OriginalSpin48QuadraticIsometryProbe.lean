import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D15OriginalSpin48QuadraticPreservationProbe
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
K1D16 — bundle the EXACT accepted source Spin48 vector action as a
genuine quadratic-form isometry of the ORIGINAL source48Quadratic.

K1D13 supplies the original real-linear equivalence. K1D15 supplies
source-exact quadratic preservation. The real-linear underlying map
is confirmed equal to K1D13, and its action equals S1V31 by rfl.

This constructs neither an SO48 group homomorphism nor determinant
+1, surjectivity, topological covering, Spin9 global lift or spectra.
Candidate only, pending independent strict source and axiom CI.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000
-- IsometryEquiv extends LinearEquiv over the fully expanded 48-label source form.
-- Bound deeper elaboration locally; this adds no proof hypotheses or axioms.
set_option maxRecDepth 4096

namespace FCP.BFSSS1V52K1D16
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- The actual original Spin48 action as a source-quadratic
isometric real-linear equivalence. Uses no replacement form. -/
noncomputable def originalSourceSpin48QuadraticIsometry (s : spinGroup Q) :
    Q.IsometryEquiv Q where
  toLinearEquiv := FCP.BFSSS1V52K1D13.originalSourceSpin48LinearEquiv s
  map_app' := by
    intro v
    exact FCP.BFSSS1V52K1D15.originalSourceSpin48VectorAction_preserves_sourceQuadratic s v

/-- No new real-linear action is introduced: the bundled quadratic
isometry's underlying real-linear equivalence is exactly K1D13. -/
theorem originalSourceSpin48QuadraticIsometry_underlyingLinearEquiv
    (s : spinGroup Q) :
    (originalSourceSpin48QuadraticIsometry s :
      Source48Vector ≃ₗ[ℝ] Source48Vector) =
      FCP.BFSSS1V52K1D13.originalSourceSpin48LinearEquiv s := by
  rfl

/-- The bundled isometry acts on every original 48-real source
vector exactly as the original S1V31 Clifford-conjugation action. -/
theorem originalSourceSpin48QuadraticIsometry_apply
    (s : spinGroup Q) (v : Source48Vector) :
    originalSourceSpin48QuadraticIsometry s v =
      FCP.BFSSS1V31.sourceSpin48VectorAction s v := by
  rfl

#print axioms originalSourceSpin48QuadraticIsometry
#print axioms originalSourceSpin48QuadraticIsometry_underlyingLinearEquiv
#print axioms originalSourceSpin48QuadraticIsometry_apply

end
end FCP.BFSSS1V52K1D16
