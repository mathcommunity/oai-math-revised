import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7COriginalSourceQuadraticIsometryEuclideanTransportProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18RSourceSpinSpecialOrthogonalWitnessProbe

/-!
K1D18V7D — source-SO witness to Euclidean isometry bridge.

The actual K1D18R original source-SO group has an original Q-isometry
witness in the original GL48, and accepted V7C can transport that exact
witness to the same-label Euclidean L2 geometry. This module exposes
that source witness and preserves its actual underlying original action.

This is a CANDIDATE pending fresh strict Lean compilation and an
independent declaration/axiom audit. It proves no determinant transport,
reflection generation, image surjectivity, covering, global Spin(9)
or BFSS spectrum.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V7D
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev GL48 := Source48Vector ≃ₗ[ℝ] Source48Vector
private abbrev Euc48 := EuclideanSpace ℝ Source48Label
private abbrev SourceSO :=
  FCP.BFSSS1V52K1D18R.source48SpecialOrthogonalWitnessGL

/-- Each genuine original sourceSO element already has an original
source-Q isometry witness, by its source-defined subgroup carrier. -/
theorem sourceSO_has_originalQ_witness (g : SourceSO) :
    ∃ i : Q.IsometryEquiv Q, (i : GL48) = (g : GL48) := by
  exact g.property.1

/-- Choose the pre-existing genuine original-Q isometry witness. -/
noncomputable def sourceSO_originalQIsometry (g : SourceSO) :
    Q.IsometryEquiv Q :=
  Classical.choose (sourceSO_has_originalQ_witness g)

/-- The chosen witness has the actual original sourceSO element
as its underlying original real-linear equivalence. -/
theorem sourceSO_originalQIsometry_underlying (g : SourceSO) :
    (sourceSO_originalQIsometry g : GL48) = (g : GL48) :=
  Classical.choose_spec (sourceSO_has_originalQ_witness g)

/-- A sourceSO element yields a genuine same-label Euclidean isometry,
using only the accepted V7C original-source transport. -/
noncomputable def sourceSO_toEuclideanIsometry
    (g : SourceSO) : Euc48 ≃ₗᵢ[ℝ] Euc48 :=
  FCP.BFSSS1V52K1D18V7C.originalSourceQIsometry_toEuclideanIsometry
    (sourceSO_originalQIsometry g)

#print axioms sourceSO_has_originalQ_witness
#print axioms sourceSO_originalQIsometry
#print axioms sourceSO_originalQIsometry_underlying
#print axioms sourceSO_toEuclideanIsometry

end
end FCP.BFSSS1V52K1D18V7D
