import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7MOriginalSourceQUnitNormalInverseTransportProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7GOriginalSourceNativeEuclideanReflectionCorrespondenceProbe

/-!
K1D18V7N — actual original source Spin(48) unit pair on arbitrary
unit normals in the exactly preserved 48-label Euclidean space.

Strictly accepted V7M: for a norm-one Euclidean u the exact inverse
coordinate vector has original source48Quadratic value 1, and its
forward source-to-Euclidean image is precisely u.
Strictly accepted V7G: the genuine original Clifford unit-pair
Spin(48) element acts as the two source-equivalent, ordered native
Euclidean hyperplane reflections. This probe composes exactly
these interfaces, with no substitution of original source Q,
Clifford source matrix, or Majorana-label order.

The first candidate is on actual original Source48Vector points.
The second is the same action transported to arbitrary genuine
Euclidean points with the native group product in exact order.

Not yet a product of many pairs, a sourceSO generator theorem,
surjectivity, topological covering, global Spin9 or BFSS spectrum.
Both roots remain CANDIDATES until full strict verification.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V7N
noncomputable section
open FCP.BFSSS1V0
open FCP.BFSSS1V52K1D18V7M
open Submodule

private abbrev Euc48 := EuclideanSpace ℝ Source48Label
private abbrev E : Source48Vector ≃ₗ[ℝ] Euc48 :=
  FCP.BFSSS1V52K1D18V7C.originalSource48ToEuclidean

/-- For ANY native Euclidean unit normals u and v, their exact
original source-Q unit inverse images determine the ACTUAL original
Clifford unit-pair Spin(48) element. Its genuine original source
vector action agrees, under E, with the exact ordered native
hyperplane reflection pair. -/
theorem originalSourceSpinUnitPair_euclideanNormals_action
    (u v : Euc48) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (w : Source48Vector) :
    E (FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry
      (FCP.BFSSS1V52K1D18V6C.originalSourceUnitPairSpin
        (originalSourceUnitNormal u) (originalSourceUnitNormal v)
        (originalSourceUnitNormal_Q_one u hu)
        (originalSourceUnitNormal_Q_one v hv)) w) =
      (ℝ ∙ u)ᗮ.reflection ((ℝ ∙ v)ᗮ.reflection (E w)) := by
  have h :=
    FCP.BFSSS1V52K1D18V7G.originalSourceSpinUnitPair_eq_nativeHyperplanePairAction
      (originalSourceUnitNormal u) (originalSourceUnitNormal v) w
      (originalSourceUnitNormal_Q_one u hu)
      (originalSourceUnitNormal_Q_one v hv)
  simpa only [originalSourceUnitNormal_roundtrip] using h

/-- Same exact original source Spin unit-pair action on ANY transported
Euclidean vector, identified with the native ordered group product
of actual Mathlib hyperplane LinearIsometryEquiv reflections. -/
theorem originalSourceSpinUnitPair_euclideanNormals_actionOnEuclidean
    (u v x : Euc48) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    E (FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry
      (FCP.BFSSS1V52K1D18V6C.originalSourceUnitPairSpin
        (originalSourceUnitNormal u) (originalSourceUnitNormal v)
        (originalSourceUnitNormal_Q_one u hu)
        (originalSourceUnitNormal_Q_one v hv)) (E.symm x)) =
      ((ℝ ∙ u)ᗮ.reflection * (ℝ ∙ v)ᗮ.reflection) x := by
  have h := originalSourceSpinUnitPair_euclideanNormals_action
    u v hu hv (E.symm x)
  simpa only [E.apply_symm_apply,
    LinearIsometryEquiv.coe_mul, Function.comp_apply] using h

#print axioms originalSourceSpinUnitPair_euclideanNormals_action
#print axioms originalSourceSpinUnitPair_euclideanNormals_actionOnEuclidean

end
end FCP.BFSSS1V52K1D18V7N
