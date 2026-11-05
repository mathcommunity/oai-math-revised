import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D3OriginalExteriorScalarCommonCoordinateKernel
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D1OriginalPolarCoordinateExteriorContractionProbe

/-!
K1D4 — apply the qualified common-coordinate-kernel theorem to the
original source-defined Spin(48) vector-action kernel.

K1D1 provides every original coordinate contraction of equivExterior(s)
as zero; K1D3 identifies that exterior element as scalar. This does NOT
identify the original Clifford scalar or prove the two-sign Spin kernel;
those require separate scalar transport and spin-membership arguments.

CANDIDATE ONLY pending fresh owner strict Lean compilation and axiom audit.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52K1D4
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev E := ExteriorAlgebra ℝ Source48Vector

/-- Under the actual source Spin(48) vector action, a trivial-action
Spin element has scalar image in the exterior algebra. -/
theorem originalSourceSpin48_trivialAction_exterior_scalar
    (s : spinGroup Q)
    (hs : ∀ v : Source48Vector,
      FCP.BFSSS1V31.sourceSpin48VectorAction s v = v) :
    ∃ c : ℝ,
      (CliffordAlgebra.equivExterior Q) (s : C) =
        algebraMap ℝ E c := by
  exact
    FCP.BFSSS1V52K1D3.originalExteriorScalar_of_all_coordinateContractions_zero
      ((CliffordAlgebra.equivExterior Q) (s : C))
      (FCP.BFSSS1V52K1D1.originalSourceSpin48_trivialAction_exteriorCoordinateContractions_zero
        s hs)

#print axioms originalSourceSpin48_trivialAction_exterior_scalar

end
end FCP.BFSSS1V52K1D4
