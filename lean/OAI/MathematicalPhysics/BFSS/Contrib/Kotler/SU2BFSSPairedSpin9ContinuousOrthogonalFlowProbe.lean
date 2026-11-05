import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9TypedOneParameterOrthogonalHomProbe
import Mathlib.Topology.Algebra.Group.Matrix

/-!
K1D18V9Y — continuity of real-parameter orthogonal flows on the
source-exact paired-Fock 48-label carrier.

Uses the pinned Matrix operator norm only as a proof interface for
NormedSpace.exp_continuous; no change of the underlying original
matrix or Fock labels. The target is the actual Mathlib orthogonal
group subtype, not just an untyped matrix statement.

These statements are real-parameter continuity, not yet a
ContinuousMonoidHom with Multiplicative real source, nor global
Spin(9) group integration, SO(48) orientation or a Spin(48) lift.
-/

set_option autoImplicit false
open scoped Matrix.Norms.Operator

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open NormedSpace

/-- The exact original 48-label matrix exponential is continuous
in its real scalar parameter, using the pinned operator norm. -/
theorem pairedMatrixExp_continuous_real
    (X : Matrix Source48Label Source48Label ℝ) :
    Continuous (fun t : ℝ => exp (t • X)) := by
  have hscalar : Continuous (fun t : ℝ => t • X) :=
    continuous_id.smul continuous_const
  exact (NormedSpace.exp_continuous :
    Continuous (exp : Matrix Source48Label Source48Label ℝ →
      Matrix Source48Label Source48Label ℝ)).comp hscalar

/-- The accepted generic V9X source-exact orthogonal-group-valued
one-parameter hom has a continuous real-parameter evaluation. -/
theorem pairedSkewOneParameterOrthogonalHom_continuous_real
    (X : Matrix Source48Label Source48Label ℝ)
    (hX : X.transpose = -X) :
    Continuous (fun t : ℝ =>
      pairedSkewOneParameterOrthogonalHom X hX
        (Multiplicative.ofAdd t)) := by
  apply Continuous.subtype_mk
  change Continuous (fun t : ℝ => exp (t • X))
  exact pairedMatrixExp_continuous_real X

/-- The original normalized paired-Fock plane-generator flow
is continuous as a map from real parameters to the actual
orthogonal-group subtype. -/
theorem normalizedPairedPlaneOneParameterOrthogonalHom_continuous_real
    (r s : SpaceIndex) :
    Continuous (fun t : ℝ =>
      normalizedPairedPlaneOneParameterOrthogonalHom r s
        (Multiplicative.ofAdd t)) := by
  exact pairedSkewOneParameterOrthogonalHom_continuous_real
    (normalizedPairedPlane r s) (normalizedPairedPlane_transpose r s)

/-- The flow of every image of the accepted canonical real LieHom
is continuous as an actual original 48-label orthogonal-group map. -/
theorem coordinateToPairedCanonicalOneParameterOrthogonalHom_continuous_real
    (A : skewAdjointMatricesLieSubalgebra
      (1 : Matrix SpaceIndex SpaceIndex ℝ)) :
    Continuous (fun t : ℝ =>
      coordinateToPairedCanonicalOneParameterOrthogonalHom A
        (Multiplicative.ofAdd t)) := by
  apply Continuous.subtype_mk
  change Continuous (fun t : ℝ =>
    exp (t • ((coordinateToPairedCanonicalSkewLieHom A) :
      Matrix Source48Label Source48Label ℝ)))
  exact pairedMatrixExp_continuous_real _

#print axioms pairedMatrixExp_continuous_real
#print axioms pairedSkewOneParameterOrthogonalHom_continuous_real
#print axioms normalizedPairedPlaneOneParameterOrthogonalHom_continuous_real
#print axioms coordinateToPairedCanonicalOneParameterOrthogonalHom_continuous_real

end
end FCP.BFSSPairedSpin9Plane
