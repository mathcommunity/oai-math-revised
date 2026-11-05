import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D2F2OriginalPBWAllContractionsNoOccupiedLabelsProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D2E5OriginalPBWEmptySupportScalarProbe

/-!
K1D3 — original 48-coordinate exterior scalar-common-kernel composition.

The independently accepted F2 theorem eliminates every nonempty PBW
coefficient from the common coordinate-contraction kernel. The independently
accepted, statement-preserving repaired E5 reconstructs a genuine scalar in
the same source-defined exterior algebra. No multiplicativity of
CliffordAlgebra.equivExterior is assumed.

CANDIDATE ONLY: not admitted without a new independent owner strict gate.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52K1D3
noncomputable section
open FCP.BFSSS1V0

private abbrev E := ExteriorAlgebra ℝ Source48Vector
private abbrev Q0 : QuadraticForm ℝ Source48Vector := 0

/-- The simultaneous kernel of all exact original 48-coordinate
exterior contractions consists only of scalar elements. -/
theorem originalExteriorScalar_of_all_coordinateContractions_zero
    (x : E)
    (hzero : ∀ j : Source48Label,
      CliffordAlgebra.contractLeft (Q := Q0)
        (LinearMap.proj j : Module.Dual ℝ Source48Vector) x = 0) :
    ∃ c : ℝ, x = algebraMap ℝ E c := by
  have hocc :
      FCP.BFSSS1V52K1D2E4.originalSourcePBWOccupiedLabels x = ∅ :=
    FCP.BFSSS1V52K1D2F2.originalSourcePBWAllContractions_zero_implies_no_occupied_labels
      x hzero
  exact FCP.BFSSS1V52K1D2E5.originalExteriorScalar_of_no_occupiedPBWLabels
    x hocc

#print axioms originalExteriorScalar_of_all_coordinateContractions_zero

end
end FCP.BFSSS1V52K1D3
